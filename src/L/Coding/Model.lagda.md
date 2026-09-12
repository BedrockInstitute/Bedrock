<!--en-->
# Coding formulas over the constructible model

An element of the constructible model `L` is not a bare set: it is an ambient set of the hierarchy `V ℓ` together with a proof that the set is constructible. So when a first-order formula is evaluated in `L`, its quantifiers range over such pairs, while the set-coded facts one actually wants, membership of a Kuratowski pair in a graph, say, are facts about the underlying sets. This chapter builds the bridge between the two readings.

The bridge has two directions. Projecting an entry outward directly discards its constructibility certificate, while transferring a bounded reader uses the absoluteness guaranteed by transitivity of `L`. Reading inward requires a witness inside the model: from a proof that a pair belongs to a constructible graph, transitivity supplies the constructibility certificate that makes the pair an element of `L`.

On top of the pair reader the chapter assembles the vocabulary of functions-as-graphs, and it is worth seeing that the clauses are logically independent. Graph application only asserts that a given ordered pair belongs to a graph. Single-valuedness says that an argument determines at most one value; it says nothing about which arguments have values. The exact-domain clause and the range restriction each constrain one further aspect. And none of these forbids a candidate graph from carrying extra elements that are not pairs at all, since these three conditions speak only about pair-shaped members; a fourth clause, that every member is a pair of an index and a value, excludes that junk. Together they form `envOverAt`, a predicate on one candidate graph relative to a domain `d` and a range `B`; it says when a given set is an environment over `d` into `B`, and does not construct the set of all environments.

The second half turns to coding. Ordered pairs and numerals can be built inside `L`, and each projects to its ambient counterpart. Since every code is a tag paired with a payload, each internal code projects to the ambient code of the formula whose constants have been projected; this compatibility is what lets the ambient readers of the earlier sections analyze codes built inside the model. A closing observation is that the whole environment description depends on its assignment only through three projected sets, so it transfers unchanged to any other assignment presenting the same graph, domain, and range; and when a code is known to be a pair, transitivity of `L` packages its two components into one constructible set.
<!--zh-->
# 可构造模型上的公式符号化

可构造模型 `L` 的元素不是裸集合：它是一个层级 `V ℓ` 中的集合，连同「该集合可构造」的证明。于是在 `L` 中求值一条一阶公式时，量词遍历的是这样的对，而人们真正想要的集合编码事实，比如某个 Kuratowski 对属于某个图，却是关于底层集合的事实。本章就在这两种读法之间架桥。

桥有两个方向。把模型元素向外投影时，可直接舍去其可构造性证书；转移有界读式时，则使用由 `L` 的传递性保证的绝对性。向内读需要在模型中给出见证：由一个对属于可构造图的证明，传递性为该对提供可构造性证书，使它成为 `L` 的元素。

在对读式之上，本章逐步建立「函数即图」的数学描述，值得注意这些条款在逻辑上各自独立。图取值只断言某个给定的有序对属于该图。单值性说一个自变量至多决定一个取值，却不涉及哪些自变量有取值。恰当定义域与取值限制各自再约束一个侧面。而且以上三条条件都不禁止候选图携带并非有序对的额外成员，因为它们只谈及对形状的成员；第四条，即每个成员都是「指标与取值」的对，把这些冗余排除在外。合在一起便是 `envOverAt`：一个相对于定义域 `d` 与值域 `B`、施于单个候选图的谓词；它刻画一个给定的集合何时是 `d` 之上取值于 `B` 的环境，并不构造全体环境的集合。

后半章转向编码。有序对与数码都能在 `L` 内部造出，且各自投影到其周遭对应物。由于每个码都是「标签配载荷」，每个内部码都投影为「常元被投影后的公式」的周遭码；正是这一相容性，使层级一侧的读式能够分析造在模型内部的码。末尾还有两个观察：整个环境描述对赋值的依赖只通过三个投影后的集合，故可原样迁移到呈现同样图、定义域与值域的任何其他赋值；而当已知一个码是对时，`L` 的传递性把它的两个分量收进一个可构造集合。
<!--ja-->
# 構成可能モデル上の論理式の符号化

構成可能モデル `L` の要素は裸の集合ではありません。それは階層 `V ℓ` の集合に、「その集合が構成可能である」という証明を添えたものです。したがって `L` の中で一階の論理式を評価するとき、量化子はこのような対を渡ります。一方、本当に欲しい集合の符号化の事実、たとえばある Kuratowski 対があるグラフに属することは、底にある集合についての事実です。本章はこの二つの読みの間に橋を架けます。

橋には二つの方向があります。模型要素を外へ射影するときは構成可能性の証明を直接忘れられますが、有界な読み式の移送には `L` の推移性が保証する絶対性を使います。内向きには模型内部の証人が必要です。対が構成可能なグラフに属するという証明から、推移性がその対の構成可能性の証明を与え、`L` の要素にします。

対の読み式の上に、本章は「関数をグラフとして」という語彙を積み上げます。ここで、これらの条項が論理的に独立していることを見ておく価値があります。グラフの適用は、与えられた順序対がグラフに属すると主張するだけです。一価性は、一つの引数が多くとも一つの値を決めると言うだけで、どの引数が値を持つかには何も言いません。ちょうどの定義域と値域の制限は、それぞれさらなる側面を制約します。しかもこれら三つの条件はどれも、対の形をした要素についてしか語らないため、対でない余計な要素を候補のグラフが持つのを禁じません。第四の条項、すべての要素が添字と値の対であること、がその余計なものを排除します。合わせたものが `envOverAt` です。これは定義域 `d` と値域 `B` に対する、一つの候補グラフについての述語であり、ある集合がいつ `d` の上、`B` への環境であるかを言うものであって、環境の全体の集合を構成するものではありません。

後半は符号化に向かいます。順序対と数項は `L` の内部で作ることができ、それぞれ周囲の対応物へ射影されます。すべての符号はタグとペイロードの対なので、内部の符号はどれも、定数を射影した論理式の周囲の符号へ射影されます。この相容性こそ、階層側の読み式が、模型の内部で作られた符号を分析できる理由です。最後に二つの観察を添えます。環境の記述全体が割り当てに依存するのは三つの射影された集合を通してだけであり、同じグラフ、定義域、値域を提示するどんな割り当てにもそのまま移ります。また、ある符号が対であると分かれば、`L` の推移性がその二つの成分を一つの構成可能集合にまとめます。
<!--/-->

<!--en-->
The two worlds sit at one universe level `ℓ`. An assignment for the inner language is a vector of elements of the carrier `S`, each an ambient set with its constructibility certificate; an ambient fact, by contrast, is stated about the underlying sets obtained by projecting every entry with `fst`. Every adequacy statement of this chapter takes the form of an identification between a satisfaction judgment at such a paired assignment and a fact about the projected one, and the projections must be handled once, correctly, before any set theory can happen.
<!--zh-->
两个世界处在同一宇宙层级 `ℓ`。内层语言的赋值是由载体 `S` 的元素组成的向量，每个元素是一个周遭集合连同其可构造性证书；而外部事实则是关于用 `fst` 把每项投影后所得的底层集合来陈述的。本章每条充分性陈述的形状，都是把「在该配对赋值处的满足判断」与「关于投影后赋值的事实」等同起来；投影必须先一次性、正确地处理完毕，集合论的论证才能开始。
<!--ja-->
二つの世界は同じ宇宙レベル `ℓ` の上にあります。内側の言語の割り当ては、台 `S` の要素からなるベクトルであり、各要素は周囲の集合に構成可能性の証明書を添えたものです。これに対して周囲の事実は、`fst` で各項目を射影して得られる底の集合について述べられます。本章の妥当性の主張はどれも、このような対の形の割り当てでの充足の判断と、射影された割り当てについての事実とを同一視する形を取ります。集合論の議論を始める前に、射影を一度、正しく処理しておかねばなりません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Model {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
Adequacy statements compare truth values, so the ambient facts are packaged as propositions. In particular, equality of two sets in the hierarchy is a proposition because the hierarchy is an h-set. Paths and congruence then align these packaged equalities with the projected lookups, while the substantive set-theoretic inputs, absoluteness, pairing, and numeral facts, enter in their own lemmas.
<!--zh-->
充分性陈述比较的是真值，故周遭事实被打包成命题。特别地，层级中两个集合的相等是命题，因为层级是 h-集合。路径与同余负责把这些包装后的等式同投影查值对齐；绝对性、配对与数码等实质集合论事实则由各自的引理提供。
<!--ja-->
妥当性の主張は真理値を比較するので、周囲の事実は命題としてまとめられます。特に階層の二集合の等しさは、階層が h-集合であるため命題です。パスと合同性がこの等しさを射影された参照とそろえ、絶対性、対、数項に関する集合論的内容はそれぞれの補題から入ります。
<!--/-->

```agda
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )
import FOL.Absoluteness
```

<!--en-->
Transitivity of `L` enters in two related ways. It underlies the Δ₀ absoluteness used to transfer bounded readers, and it constructs model witnesses from members of constructible sets. A direct projection needs no new witness, but the formula transfer that justifies the outward reading still rests on this transitivity theorem.
<!--zh-->
`L` 的传递性以两种相关方式进入论证：它是转移有界读式所需 Δ₀ 绝对性的基础，也把可构造集合的成员组成模型内见证。直接投影本身不需要新见证，但向外读取公式所依赖的转移定理仍以传递性为依据。
<!--ja-->
`L` の推移性は二つの関連した仕方で使われます。有界な読み式を移す Δ₀ 絶対性の基礎となり、また構成可能集合の要素から模型内の証人を作ります。直接の射影に新しい証人は要りませんが、論理式を外向きに読む移送定理はこの推移性に依存します。
<!--/-->

```agda
import FOL.Coding
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; module VCode )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
```

<!--en-->
The outward direction for bounded formulas is supplied by absoluteness: a Δ₀ formula about the hierarchy, whose constants name constructible sets, has the same meaning when read in `L`, and the two readings agree by a path. The pair reader is of exactly this kind, so its satisfaction in the model is identified with an equation between projected sets. The inward direction has no general shortcut; it is supplied per entry by an explicit construction of a witness, and the pair case is the one this chapter needs.
<!--zh-->
有界公式的向外方向由绝对性承担：一条关于层级、且常元命名可构造集合的 Δ₀ 公式，在 `L` 中读出时意义不变，两种读法经一条路径一致。对读式正是这种公式，故它在模型中的满足被等同于投影后集合间的等式。向内方向没有一般捷径，只能逐词条显式构造见证；本章所需的正是对这一例。
<!--ja-->
有界論理式の外向きの方向は絶対性が担います。階層についての Δ₀ 論理式で、定数が構成可能な集合を名指すものは、`L` の中で読んでも意味が変わらず、二つの読みは一つの経路として一致します。対の読み式はまさにこの種の式なので、模型の中での充足は射影された集合の間の等式と同一視されます。内向きの方向に一般的な近道はなく、項目ごとに証明を明示的に構成するしかありません。本章が必要とするのは対の場合です。
<!--/-->

```agda
open import L.Absoluteness {ℓ} using ( liftFo; transferFo )
open import L.Coding.PairFormulas {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate; ∈pair-introL; ∈pair-introR )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )
```

<!--en-->
Some existence statements in the chapter are deliberately weak. When a graph member is said to exist, the claim is merely that some entry exists, not a chosen one: such statements live in propositional truncation and can be eliminated only into proposition-valued targets. Keeping truncated existence distinct from an explicit witness matters in both directions of every adequacy proof, since satisfaction of an existential formula always has the truncated shape.
<!--zh-->
本章中的一些存在性陈述是刻意弱的。说「图中存在一个条目」时，主张仅仅是某个条目存在，而非选定一个：这类陈述居于命题截断之中，只能消去到取命题值的对象。把被截断的存在与显式见证区分开，在每条充分性证明的两个方向上都重要，因为存在公式的满足总是取截断的形状。
<!--ja-->
本章の存在主張の一部は、意図的に弱く作られています。グラフに項目が存在すると言うとき、主張するのはある項目が単に存在することであって、どれかを選び出すことではありません。このような主張は命題的截断の中に住み、命題値の対象へしか消去できません。截断された存在と明示的な証人を区別しておくことは、すべての妥当性の証明の両方向で重要です。存在の公式の充足は常に截断された形を持つからです。
<!--/-->

```agda

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
Truth values are propositions at level `ℓ-suc ℓ`: a formula does not evaluate to a boolean but to an `hProp`, packaging an underlying type with the proof that it is a proposition. The carrier `S` of the inner structure is thereby fixed as well: its elements are exactly the pairs of an ambient set and a constructibility certificate. Throughout what follows, `γ ⊨ φ` means satisfaction in the constructible model, and `⟦ t ⟧ γ` is an element of `S`, a set with its certificate.
<!--zh-->
真值是层 `ℓ-suc ℓ` 上的命题：公式不取值为布尔值，而取值为一个 `hProp`，即底层类型连同「它是命题」的证明的包装。由此内层结构的载体 `S` 也随之固定：它的元素恰是环境集合与可构造性证书组成的对。此后，`γ ⊨ φ` 一律指在可构造模型中的满足，而 `⟦ t ⟧ γ` 是 `S` 的元素，即一个集合连同其证书。
<!--ja-->
真理値はレベル `ℓ-suc ℓ` の命題です。論理式はブール値ではなく `hProp` に評価され、それは底にある型と「それが命題である」ことの証明を包んだものです。これにより内側の構造の台 `S` も固定されます。その要素は、周囲の集合と構成可能性の証明書の対にほかなりません。以後、`γ ⊨ φ` は構成可能モデルにおける充足を意味し、`⟦ t ⟧ γ` は `S` の要素、すなわち証明書を伴う集合です。
<!--/-->

```agda
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
One more structural fact shapes the statements: every reader of this chapter is stated through `fst` of a lookup and nothing else. That is, satisfaction in the model is always compared with facts about underlying sets, never with anything internal to the certificates. The same principle makes the final transport lemma possible: if two assignments present the same three underlying sets where a description looks, the description cannot tell the assignments apart.
<!--zh-->
还有一个结构性事实规定了所有陈述的形状：本章每条读式都只经查表的 `fst` 陈述，别无其他。也就是说，模型中的满足总是与关于底层集合的事实相比较，从不与证书内部的任何东西比较。同一条原则也使最后的迁移引理成为可能：若两个赋值在一条描述所查看之处呈现同样的三个底层集合，这条描述就无法区分这两个赋值。
<!--ja-->
もう一つ、主張の形を定める構造的な事実があります。本章の読み式はどれも、検表の `fst` を通してのみ述べられ、それ以外の何ものも通りません。つまり、模型の中での充足は常に底の集合についての事実と比較され、証明書の内部の何かと比較されることはありません。同じ原則が最後の輸送の補題を可能にします。記述が参照する場所で同じ三つの底の集合を提示する割り当てどうしを、記述は区別できないのです。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )
```

<!--en-->
## Looking up in a projected environment

Every adequacy statement of this chapter compares a satisfaction judgment at an assignment of model elements with an ambient fact about the *projected* assignment, in which each entry has been stripped of its constructibility certificate by `fst`. The two assignments are not the same object, so before any comparison can be made one must know that looking up a variable in the projected assignment gives the projection of looking it up in the original. That is the whole content of the lemma below, and it enters every adequacy proof that follows, wherever an ambient equation has to be rephrased in terms of the entries of `γ` themselves.
<!--zh-->
## 在投影后的环境中查表

本章的每条充分性陈述，都是把「模型元素赋值处的满足判断」与「关于**投影后**赋值的外部事实」相比较：后者把每一项的证书用 `fst` 剥去。这两个赋值并非同一个对象，因此在做任何比较之前，必须知道：在投影后的赋值中查某变元所得，等于在原赋值中查它再投影。这正是下面这条引理的全部内容；其后凡需把外部等式改用 `γ` 自身的条目来陈述之处，都会用到它。
<!--ja-->
## 射影した環境での参照

本章の妥当性の主張はどれも、模型の要素からなる割り当てでの充足の判断を、**射影された**割り当てについての周囲の事実と比較します。射影された割り当てでは、各項目から `fst` によって構成可能性の証明書が剥ぎ取られています。二つの割り当ては同じ対象ではないので、比較を行う前に、射影された割り当てで変数を参照した結果が、元の割り当てで参照したものを射影したものに等しいことを知っておかねばなりません。以下の補題の内容はまさにそれだけです。この後、周囲の等式を `γ` 自身の項目で言い換えねばならないところでは、必ずこれが登場します。
<!--/-->

<!--en-->
The proof is a recursion on the position `i`. At position `zero`, both sides reduce to the head of the list: `lookup zero (x ∷ γ)` is `x`, `map fst` of the cons is the cons of the projections, and the two first projections of `x` agree definitionally, hence `refl`. At a successor position, both lookups advance one entry and the recursive call finishes the argument. Nothing here uses constructibility; the lemma holds for any environment of pairs.
<!--zh-->
证明对位置 `i` 作递归。在位置 `zero`，两边都化归到表头：`lookup zero (x ∷ γ)` 就是 `x`，cons 的 `map fst` 是诸投影的 cons，而 `x` 的两次取首分量按定义相等，故得 `refl`。在后继位置，两次查表各前进一项，递归调用完成论证。这里没有用到可构造性；该引理对任何由对构成的环境都成立。
<!--ja-->
証明は位置 `i` に対する再帰です。位置 `zero` では両辺ともリストの先頭に簡約されます。`lookup zero (x ∷ γ)` は `x` であり、cons の `map fst` は射影の cons であり、`x` の二度の第一射影は定義的に等しいので `refl` が得られます。後続の位置では、二つの参照がともに一項目進み、再帰呼び出しが議論を完成させます。ここで構成可能性はまったく使われず、この補題は対からなる任意の環境に対して成り立ちます。
<!--/-->

```agda
lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
           → lookup i (map fst γ) ≡ fst (lookup i γ)
lookup-fst zero    (x ∷ γ) = refl
lookup-fst (suc i) (x ∷ γ) = lookup-fst i γ
```

<!--en-->
## The ordered pair

The bridge this chapter builds runs in two directions. Forward, a satisfaction judgment in the model, evaluated at an assignment whose entries are elements of the model, must be converted into a fact about sets of the hierarchy; the entries are first projected by `fst`, so the ambient statement is always about projected values. The first entry of the dictionary is the recognition of ordered pairs: the ambient reader `prAt q u v` says that the value at position `q` is the Kuratowski pair of the values at `u` and `v`. Because this reader is bounded (Δ₀), its meaning is absolute, so reading it in the language of `L` costs nothing; and since it names no constants, the lift imposes no conditions on them. The theorem states the outcome exactly: satisfaction of the lifted reader in the model is a path to the equality of the projected value at `q` with `pr` of the projected values at `u` and `v`. The reverse direction, where a bare ambient membership must be converted back into a witness living inside the model, first appears in the next section, and there transitivity of `L` does the work.
<!--zh-->
## 有序对

本章要搭的桥有两个方向。正向，模型中的一个满足判断 (在元素为模型元素的赋值处求值) 必须转化为关于层级集合的事实；各赋值项先用 `fst` 投影，故环境陈述始终针对投影后的取值。词典的第一个词条识别有序对：周遭读式 `prAt q u v` 说 `q` 处的取值正是 `u`、`v` 两处取值的 Kuratowski 对。这条读式是有界 (Δ₀) 的，其意义具有绝对性，因而改在 `L` 的语言中读出毫无代价；它又不含任何常元，抬升便对常元不施加任何条件。定理精确地陈述结果：抬升后的读式在模型中的满足，是一条通往「`q` 处投影值等于 `u`、`v` 处投影值之 `pr`」的路径。反方向，即把一条赤裸的周遭隶属转回生活在模型内部的见证，要到下一节才首次出现，那时由 `L` 的传递性承担工作。
<!--ja-->
## 順序対

本章が築く橋には二つの方向があります。順方向には、模型の中での充足の判断、つまり各項目が模型の要素である割り当てのもとで評価された判断を、階層の集合についての事実へ変えなければなりません。各項目はまず `fst` で射影されるので、周囲の主張は常に射影された値について述べられます。辞書の最初の項目は順序対の認識です。周囲の読解式 `prAt q u v` は、位置 `q` の値が位置 `u` と `v` の値の Kuratowski 対であると言います。この読解式は有界 (Δ₀) なので意味は絶対的であり、`L` の言語で読んでも何の代償もありません。また定数をまったく名指さないので、持ち上げは定数にいかなる条件も課しません。定理はその帰結を正確に述べます。持ち上げられた読解式の模型の中での充足は、「位置 `q` の射影された値が `u` と `v` の射影された値の `pr` に等しい」という等式へのパスです。逆方向、すなわち裸の周囲の所属を模型の内部に住む証人へ戻す方向は、次の節で初めて現れ、そこでは `L` の推移性が働きます。
<!--/-->

<!--en-->
The statement compares truth values, so its right-hand side must be a truth value too. Equality of two sets of the hierarchy is a proposition because the hierarchy is an h-set, and `PairIs` packages such a path type with exactly that propositionhood proof. The lifted reader `prAtL q u v` is `prAt q u v` itself with each constant relabelled into the carrier `S`; here there are no constants to relabel, but the boundedness certificate `Δ₀-prAt` still travels with the formula, since the transfer lemma demands one.
<!--zh-->
该陈述比较的是真值，故右边本身也必须是一个真值。层级中两个集合的相等是命题，因为层级是 h-集合；`PairIs` 把这样的路径类型连同「它是命题」的证明包装起来。抬升后的读式 `prAtL q u v` 就是 `prAt q u v` 本身，只是把每个常元改名进载体 `S`；这里没有可改名的常元，但有界性证书 `Δ₀-prAt` 仍随公式携带，因为转换引理要求一份这样的见证。
<!--ja-->
この主張は真理値を比較するので、右辺も真理値でなければなりません。階層の二つの集合の等式は、階層が h-集合であるため命題であり、`PairIs` はそのようなパスの型にちょうどその命題性の証明を包んで記録します。持ち上げられた読解式 `prAtL q u v` は、各定数を台 `S` へ改名した `prAt q u v` そのものです。ここには改名すべき定数がありませんが、有界性の証明書 `Δ₀-prAt` は依然として公式に伴われます。転送の補題がそれを要求するからです。
<!--/-->

```agda
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

prAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAtL q u v = liftFo (prAt q u v) _
```

<!--en-->
The adequacy statement equates, by a single path, satisfaction of the reader in the model with the packaged equality on the right. Note where the projections stand: the assignment `γ` consists of elements of `S`, and the equation is stated about `fst` of the looked-up entries. That is the shape every entry of this dictionary takes, because the concrete membership facts live in the hierarchy, not inside the model's carrier.
<!--zh-->
充分性陈述用一条路径把读式在模型中的满足与右边的包装等式等同起来。注意投影所处的位置：赋值 `γ` 由 `S` 的元素组成，而等式是关于所查各项的 `fst` 陈述的。这部词典的每个词条都取这个形状，因为具体的隶属事实生活在层级中，而不在模型的载体内。
<!--ja-->
妥当性の主張は、一本のパスによって、読解式の模型の中での充足と右辺のパッケージ化された等式を等しくします。射影がどこに立っているか注意してください。割り当て `γ` は `S` の要素からなり、等式は参照された項目の `fst` について述べられています。この辞書のどの項目もこの形を取ります。具体的な所属の事実が模型の台の内側ではなく階層に住んでいるからです。
<!--/-->

```agda

prAtL-adequate : ∀ {n} (q u v : Fin n) (γ : S ^ n)
  → (γ ⊨ prAtL q u v)
  ≡ PairIs (fst (lookup q γ)) (pr (fst (lookup u γ)) (fst (lookup v γ)))
prAtL-adequate q u v γ =
    transferFo (prAt q u v) _ (Δ₀-prAt q u v) γ
```

<!--en-->
The proof composes three paths and introduces nothing new. The transfer lemma first equates satisfaction in `L` with ambient satisfaction of `prAt q u v` at the projected assignment, using the boundedness certificate. The reader's own adequacy theorem then rewrites that ambient satisfaction as the equality of the interpreted values. Finally the two lookups of the projected assignment are moved to projections of the lookups in `γ`, and the equation is reassembled under `PairIs` by congruence. The result is exactly the promised identification.
<!--zh-->
证明串联三条路径，未引入任何新内容。转换引理先借有界性证书，把 `L` 中的满足等同于 `prAt q u v` 在投影后赋值处的周遭满足。随后读式自身的充分性定理把那个周遭满足改写为被解释值之间的等式。最后，投影后赋值中的两次查表被换成 `γ` 中查表后的投影，再由同余把等式在 `PairIs` 之下重新组装。所得正是所允诺的等同。
<!--ja-->
証明は三つのパスを連結するだけで、新しいものは何も導入しません。まず転送の補題が有界性の証明書を使って、`L` の中での充足を、射影された割り当てでの `prAt q u v` の周囲の充足と等しいとします。次に読解式自身の妥当性定理が、その周囲の充足を解釈された値の間の等式へ書き換えます。最後に、射影された割り当てでの二度の参照を `γ` での参照の射影へ移し、合同によって等式を `PairIs` の下で組み立て直します。得られるのは約束された同一視そのものです。
<!--/-->

```agda
  ∙ prAt-adequate q u v (map fst γ)
  ∙ cong₂ PairIs (lookup-fst q γ)
      (cong₂ pr (lookup-fst u γ) (lookup-fst v γ))
```

<!--en-->
## Application

A graph in the object language is a set of ordered pairs, and the question every later use asks of one is whether a given pair belongs to it. The reader below expresses exactly that as a bounded existential, over the members of whatever set a term denotes, with the pair reader as its body. Its meaning is the ambient membership of the Kuratowski pair in the graph's underlying set.

The forward direction converts satisfaction into membership. The backward direction is where the model does real work: to satisfy the existential one must produce an *element of the model* whose underlying set is the pair, while the hypothesis supplies only a set. The pair is constructible because it belongs to a constructible set and the constructible class is transitive. This one step is the whole argument, and it recurs wherever a witness must be produced inside the model rather than merely in the hierarchy.
<!--zh-->
## 取值

对象语言中的图是有序对的集合，而使用图时，要问的都是某个给定的对是否属于它。下面的读式把这件事表达为一个有界存在：在某词项所指集合的成员范围内存在一员，其主体为对读式。它的含义是那个 Kuratowski 对属于图的底层集合这一周遭隶属。

正向把满足转化为隶属。反方向才是模型真正发挥作用之处：要满足那个存在量词，必须给出一个**模型的元素**，其底集正是那个对，而假设只提供了一个集合。这个对可构造，因为它属于某个可构造集合，而可构造类是传递的。这一步就是全部论证；此后凡要求见证造在模型之内、而非仅在层级之内，都会重复这一步。
<!--ja-->
## グラフの適用

対象言語におけるグラフは順序対の集合であり、後の使用が問うのは常に、与えられた対がそれに属するかどうかです。以下の読解式はこれを有界な存在量化として表します。ある項が指す集合の要素の範囲で一つの要素が存在し、その本体が対の読解式であるというものです。その意味は、Kuratowski 対がグラフの底にある集合に属するという周囲の所属です。

順方向は充足を所属へ変えます。逆方向こそ模型が実際に働く場所です。存在量化を充足するには、底にある集合がその対であるような**模型の要素**を与えねばならず、仮定が供するのは集合にすぎません。この対が構成可能なのは、構成可能な集合に属し、構成可能なクラスが推移的だからです。この一段階が議論のすべてであり、証人が階層の中だけでなく模型の内部に作られねばならない場面では、同じ段階が繰り返されます。
<!--/-->

<!--en-->
The definition reads: there merely exists a member of the graph, bounded by the value of the term `F`, satisfying the pair reader. The bound entry of the existential extends the environment, and the three positions of the pair reader name that entry together with the shifted references to the two arguments, while the bound `F` denotes the graph over which the fresh entry ranges.
<!--zh-->
定义读作：在该词项 `F` 的值为界的范围内，仅仅存在图的一个成员，满足对读式。存在量词的约束项扩展了环境；对读式的三个位置指称这个新项以及两个论元平移后的引用，而界 `F` 指定这个新条目所遍历的图。
<!--ja-->
定義は次のように読みます。項 `F` の値で限られた範囲の中に、グラフの要素が単にひとつ存在し、対の読解式を満たす、と。存在量化の束縛された項目が環境を伸ばし、対の読解式の三つの位置はその項目と、二つの引数のずらされた参照を指します。`F` 自身は、量化子が施したずらしの下で拡張環境の中で評価されます。
<!--/-->

```agda
private
  appTerm : ∀ {n} → Term S n → Fin n → Fin n → Formula S n
  appTerm F x y = ∃̇∈ F (prAtL zero (suc x) (suc y))

  appTerm-adequate : ∀ {n} (F : Term S n) (x y : Fin n) (γ : S ^ n)
    → (γ ⊨ appTerm F x y)
```

<!--en-->
The adequacy statement names the ingredients. Here `a` and `b` are the projected values of the two argument slots, and `G` is the interpretation of the term: an element of `S`, hence a set carrying its constructibility certificate, whose underlying set is the graph. The claim is a path of truth values between satisfaction and an ambient membership: the pair `pr a b` belongs to the underlying set of the graph.
<!--zh-->
充分性陈述点名各成分。`a` 与 `b` 是两个论元槽位的投影值，`G` 是该词项的解释：它是 `S` 的元素，即一个携带可构造性证书的集合，其底层集合就是那个图。所断言的是一条真值路径，连接满足关系与一个周遭隶属：对 `pr a b` 属于图的底层集合。
<!--ja-->
妥当性の主張は材料に名前を付けます。`a` と `b` は二つの引数スロットの射影された値であり、`G` は項の解釈です。それは `S` の要素、つまり構成可能性の証明書を担う集合であり、その底にある集合がグラフです。主張されるのは、充足と周囲の所属、すなわち対 `pr a b` がグラフの底にある集合に属することとの間の、真理値のパスです。
<!--/-->

```agda
    ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (⟦ F ⟧ γ))
  appTerm-adequate F x y γ = ⇔toPath fwd bwd
    where
    a = fst (lookup x γ)
    b = fst (lookup y γ)
```

<!--en-->
The auxiliary `read` unpacks one existential fiber. Given an element `z` of the model and a proof that the extended assignment satisfies the pair reader, the adequacy theorem already proved for the pair reader transports that proof to the proposition that the underlying set of `z` equals `pr a b`. The forward direction receives, after unfolding the bounded existential's satisfaction, a truncated pair of a membership `z∈G` and such a reader proof; eliminating the truncation is legitimate because the target membership is a proposition, and inside the branch the membership is transported along the path that `read` supplies.
<!--zh-->
辅助工具 `read` 拆开存在量词的一个纤维。给定模型的一个元素 `z`，以及「扩展赋值满足对读式」的证明，上一节的充分性定理把该证明传输到「`z` 的底层集合等于 `pr a b`」这一命题。展开有界存在的满足关系后，前进方向收到的是隶属 `z∈G` 与这样一份读式证明的截断对；由于目标是取命题值的隶属，消去截断是合法的，而在分支内部，隶属沿 `read` 给出的路径传输。
<!--ja-->
補助の `read` は存在量化の一つのファイバーをほどきます。模型の要素 `z` と、拡張された割り当てが対の読解式を充足することの証明が与えられれば、前節の妥当性定理がその証明を、「`z` の底にある集合は `pr a b` に等しい」という命題へ輸送します。有界な存在量化の充足を展開すると、順方向は所属 `z∈G` とそのような読解式の証明の切り詰められた対を受け取ります。目標の所属が命題であるため截断の消去は正当であり、分岐の中では所属が `read` の供給するパスに沿って輸送されます。
<!--/-->

```agda
    G = ⟦ F ⟧ γ

    read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
    read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

    fwd : ⟨ γ ⊨ appTerm F x y ⟩ → ⟨ pr a b ∈ fst G ⟩
    fwd = PT.rec (snd (pr a b ∈ fst G))
```

<!--en-->
The backward direction is where the constructible model enters. From a bare membership proof `⟨ pr a b ∈ fst G ⟩` one must produce a proof of the truncated existential, and its first component cannot be the set `pr a b` itself, which is a set of the hierarchy and not an element of `S`. The witness is built in the next lines; the displayed branch packages the membership with a reader proof obtained by transporting `refl` backwards through the adequacy path, which is legitimate because the underlying set of the witness is definitionally `pr a b`.
<!--zh-->
反方向才是可构造模型登场之处。从一条赤裸的隶属证明 `⟨ pr a b ∈ fst G ⟩` 出发，必须给出截断存在的一个证明，而其第一个分量不能是集合 `pr a b` 本身：那是层级中的集合，不是 `S` 的元素。见证将在随后几行构造；这里展示的分支把隶属与一份读式证明打包，后者是把 `refl` 沿充分性路径反方向传输得到的，之所以合法，是因为见证的底层集合按定义就是 `pr a b`。
<!--ja-->
逆方向こそ、構成可能モデルが登場する場面です。裸の所属の証明 `⟨ pr a b ∈ fst G ⟩` から、切り詰められた存在量化の住人を与えなければなりませんが、その第一成分は集合 `pr a b` そのものではいけません。それは階層の集合であって `S` の要素ではないからです。証人は次の行で作られます。ここに示された分岐は、所属と読解式の証明を一つに包みます。後者の証明は `refl` を妥当性のパスを逆向きに輸送して得られるもので、証人の底にある集合が定義的に `pr a b` であるため、これで構いません。
<!--/-->

```agda
      (λ { (z , (z∈G , h)) → subst (λ w → ⟨ w ∈ fst G ⟩) (read z h) z∈G })

    bwd : ⟨ pr a b ∈ fst G ⟩ → ⟨ γ ⊨ appTerm F x y ⟩
    bwd h = ∣ zS , (h , subst ⟨_⟩
        (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
      where
```

<!--en-->
The witness is the one genuinely model-specific construction of this section. To present `pr a b` as an element of `S`, one needs a constructibility certificate for it. The hypothesis says the pair belongs to the underlying set of `G`, and `G` carries its own certificate; transitivity of the constructible class turns these two facts into `isL (pr a b)`. A member of a constructible set is constructible. With the witness in place, the public form `appAt` fixes the graph to sit in a variable slot, reading the term `var f`, and its adequacy is just the general theorem at that particular term: membership of the projected pair in the underlying set of the value at slot `f`.
<!--zh-->
见证是本节唯一真正属于模型的构造。要把 `pr a b` 呈现为 `S` 的元素，需要它的可构造性证书。假设说这个对属于 `G` 的底层集合，而 `G` 自带证书；可构造类的传递性把这两个事实变成 `isL (pr a b)`。可构造集合的成员是可构造的。见证就位后，公开形式 `appAt` 把图固定在变元槽位上，即取词项 `var f`；其充分性就是一般定理在该特定词项上的实例：投影对属于槽位 `f` 处取值的底层集合。
<!--ja-->
証人は、この節で唯一、真に模型に固有の構成です。`pr a b` を `S` の要素として提示するには、その構成可能性の証明書が必要です。仮定はこの対が `G` の底にある集合に属すると述べ、`G` は自身の証明書を担っています。構成可能なクラスの推移性がこの二つの事実を `isL (pr a b)` へ変えます。構成可能な集合の要素は構成可能なのです。証人が揃ったところで、公開形式 `appAt` はグラフを変数のスロットに固定し、項 `var f` を読みます。その妥当性は、特定の項における一般定理の実例、すなわち射影された対がスロット `f` の値の底にある集合に属することにほかなりません。
<!--/-->

```agda
      zS : S
      zS = pr a b , isL-trans {x = fst G} {y = pr a b} h (G .snd)

appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
appAt f = appTerm (var f)

appAt-adequate : ∀ {n} (f x y : Fin n) (γ : S ^ n)
```

<!--en-->
This specialization matters because the remaining graph predicates refer to their graph through an assignment slot. After projection, every such occurrence has the uniform form `pr (fst x) (fst y) ∈ fst (lookup f γ)`, so the later single-valuedness and domain arguments can use one membership statement throughout.
<!--zh-->
这一特化使后面的图谓词都能通过赋值槽位引用其图。投影后，每次引用统一写成 `pr (fst x) (fst y) ∈ fst (lookup f γ)`，因此单值性与定义域论证可以始终使用同一种隶属陈述。
<!--ja-->
この特殊化により、後のグラフ述語は割り当てのスロットを通してグラフを参照できます。射影後の各出現は一様に `pr (fst x) (fst y) ∈ fst (lookup f γ)` となるので、一価性と定義域の議論では同じ所属の形を一貫して使えます。
<!--/-->

```agda
  → (γ ⊨ appAt f x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
appAt-adequate f = appTerm-adequate (var f)
```

<!--en-->
The graph being read need not sit in a variable slot; it may be a fixed element of the model named directly. The constant term `con F` is exactly that, and the adequacy statement simplifies accordingly: since the constant is interpreted as the element `F` itself, the right-hand side is membership in `fst F`, with no reference to the environment for the graph.
<!--zh-->
被读的图不必落在变元槽位中；它也可以是模型的一个固定元素，被直接命名。常元词项 `con F` 正是如此，而充分性陈述随之简化：由于常元被解释为元素 `F` 本身，右边就是属于 `fst F` 的隶属，完全不再涉及环境中关于图的项。
<!--ja-->
読む対象となるグラフは、変数のスロットにある必要はなく、模型の固定された要素として直接名指されても構いません。定数の項 `con F` はまさにそれであり、妥当性の主張はそれに応じて簡単になります。定数は要素 `F` そのものとして解釈されるので、右辺は `fst F` への所属となり、グラフのための環境の項目にはまったく触れません。
<!--/-->

<!--en-->
The definition instantiates the shared reader at `con F`. Because the constant is interpreted as itself, the bounded existential ranges directly over the members of `fst F`, and the adequacy statement records exactly that: satisfaction is a path to the membership of the projected pair of the two argument values in `fst F`. The membership on the right is ambient membership after projection; the existential on the left still quantifies over elements of the model.
<!--zh-->
定义在 `con F` 处实例化共用读式。由于常元被解释为它自身，有界存在直接遍历 `fst F` 的成员，充分性陈述也如实记录这一点：满足关系是一条通往「两个论元值的投影对属于 `fst F`」的路径。右边的隶属是投影后的周遭隶属；左边的存在量词仍在模型的元素上取值。
<!--ja-->
定義は共通の読解式を `con F` で実例化します。定数はそれ自身として解釈されるため、有界な存在量化は `fst F` の要素を直接渡ります。妥当性の主張はまさにそれを記録します。充足は、二つの引数の値の射影された対が `fst F` に属することへのパスです。右辺の所属は射影後の周囲の所属であり、左辺の存在量化子は依然として模型の要素の上を渡ります。
<!--/-->

```agda
appC : ∀ {n} → S → Fin n → Fin n → Formula S n
appC F = appTerm (con F)

appC-adequate : ∀ {n} (F : S) (x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appC F x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst F)
```

<!--en-->
The proof is the shared adequacy theorem at the constant term, and needs no argument of its own. Together with `appAt`, the dictionary now recognizes pair membership in a graph given by a slot and in a graph given as a fixed element, each with its exact meaning as an ambient membership.
<!--zh-->
证明就是在常元词项上使用共用充分性定理，自身无需任何论证。与 `appAt` 一道，词典如今同时识别由槽位给出的图与由固定元素给出的图中的对隶属，且各自的意义都精确地是一个周遭隶属。
<!--ja-->
証明は定数の項における共通の妥当性定理であり、自前の議論を何も必要としません。`appAt` と合わせて、辞書はこれで、スロットによって与えられたグラフの中の対の所属と、固定された要素として与えられたグラフの中の対の所属の両方を認識し、それぞれの意味が正確に周囲の所属となっています。
<!--/-->

```agda
appC-adequate F = appTerm-adequate (con F)
```

<!--en-->
## Single-valuedness

A graph is single-valued when any two pairs in it with the same first component have the same second component. This is a statement purely about membership of pairs; it neither says that the graph has any members at all nor that a given argument occurs in it, so it is logically independent of the domain condition that comes later.

The claim is stated as two directions rather than a single path, in the form in which it is actually consumed: reading outward, from the object-language assertion to an equation between the underlying sets of two values recorded against the same argument.
<!--zh-->
## 单值性

一个图是单值的，如果其中任意两个第一分量相同的对具有相同的第二分量。这条陈述只谈对之间的隶属；它既不说图有成员，也不说某个给定的论元在图中出现，因此与稍后的定义域条件在逻辑上相互独立。

该断言陈述为两个方向而非一条路径，取的正是它实际被使用的形式：向外读，即从对象语言的断言得到「记在同一论元下的两个取值的底层集合相等」这一等式。
<!--ja-->
## 一価性

グラフが一価であるとは、その中の第一成分の等しい任意の二つの対が、第二成分も等しいということです。これは対の所属についてだけの主張であり、グラフが要素を持つことも、与えられた引数が現れることも言わないので、後で現れる定義域の条件とは論理的に独立です。

この主張は一本のパスではなく二つの方向として述べられます。実際に使われる形、すなわち対象言語の主張から、同じ引数に対して記録された二つの値の底にある集合の等式へと外向きに読み出す形です。
<!--/-->

<!--en-->
Read from the outside in: for all `x`, for all `y`, for all `y'`, if the pair of `x` and `y` belongs to the graph then, if the pair of `x` and `y'` also belongs, the values `y` and `y'` are equal. The equality demanded is between the underlying sets of the two values, since `y` and `y'` are themselves elements of the model. Nothing here says the graph is inhabited, or that every argument has a value; that is the separate domain condition.
<!--zh-->
由外向内读：对一切 `x`、`y`、`y'`，若 `x` 与 `y` 的对属于该图，且 `x` 与 `y'` 的对也属于，则取值 `y` 与 `y'` 相等。所要求的相等是两个取值的底层集合之间的相等，因为 `y` 与 `y'` 本身是模型的元素。这里没有说图非空，也没有说每个论元都有取值；那是独立的定义域条件。
<!--ja-->
外側から読みます。すべての `x`、`y`、`y'` に対し、`x` と `y` の対がグラフに属し、かつ `x` と `y'` の対も属するなら、値 `y` と `y'` は等しい、ということです。要求される等式は、二つの値の底にある集合の間の等式です。`y` と `y'` はそれ自体模型の要素だからです。ここにはグラフが空でないことも、すべての引数が値を持つことも述べられていません。それは独立した定義域の条件です。
<!--/-->

```agda
svAt : ∀ {n} → Fin n → Formula S n
svAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
  ⇒̇ (appAt (suc (suc (suc f))) (suc (suc zero)) zero
  ⇒̇ (var (suc zero) ≐ var zero)))))
```

<!--en-->
The two directions are stated for a fixed graph slot `f` and a fixed environment `γ`, so a local predicate records the external meaning once. `Holds x y` says that the projected pair of `x` and `y` belongs to the underlying set of the graph; this is exactly the shape one application of `appAt-adequate` produces. The two adequacy instances that follow fix which of the two implications is being read: `at` for the pair with the value `y`, `at'` for the pair with `y'`.
<!--zh-->
两个方向都相对于固定的图槽位 `f` 与固定环境 `γ` 陈述，故用一个局部谓词把外部含义记录一次。`Holds x y` 说 `x` 与 `y` 的投影对属于图的底层集合；这正是 `appAt-adequate` 一次应用所产出的形状。随后两个充分性实例分别固定所读的是哪一支：`at` 对应带取值 `y` 的对，`at'` 对应带 `y'` 的对。
<!--ja-->
二つの方向は、固定されたグラフのスロット `f` と固定された環境 `γ` に対して述べられるので、局所的な述語が外部の意味を一度記録します。`Holds x y` は、`x` と `y` の射影された対がグラフの底にある集合に属することを言い、これは `appAt-adequate` を一度適用して得られる形そのものです。続く二つの妥当性の実例は、どちらの含意を読んでいるのかを固定します。`at` は値 `y` を持つ対のためのもので、`at'` は `y'` を持つ対のためのものです。
<!--/-->

```agda

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds : S → S → Type (ℓ-suc ℓ)
    Holds x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at : (x y y' : S)
```

<!--en-->
Each helper is an instance of the application adequacy at the environment extended by the three quantified elements, which shifts the indices of the formula accordingly. Because `at` and `at'` are paths between propositions, a proof can be moved from either side to the other by transport; the two direction lemmas below do exactly this, in opposite orientations.
<!--zh-->
两个辅助命题都是在以三个被量化元素扩展后的环境处应用充分性的实例，公式的下标随之平移。由于 `at` 与 `at'` 是命题之间的路径，证明可以沿任一方向传输；下面两个方向引理做的正是这件事，只是取向相反。
<!--ja-->
各補助命題は、三つの量化された要素で拡張した環境での妥当性の実例であり、公式の添字はそれに応じてずれます。`at` と `at'` は命題の間のパスなので、証明はどちらの側からでも輸送で移せます。以下の二つの方向の補題がするのはまさにそれで、向きが逆なだけです。
<!--/-->

```agda
       → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero))
       ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero)
                  (y' ∷ y ∷ x ∷ γ)

    at' : (x y y' : S)
```

<!--en-->
Reading the object-language claim outward gives the usable conclusion. Given satisfaction of `svAt f`, the quantifiers supply the implication for arbitrary elements `x`, `y`, `y'` of the model; feeding it the two memberships `Holds x y` and `Holds x y'`, each first transported from its external form into the satisfaction the quantifiers expect, yields the equality `fst y ≡ fst y'` of the two underlying values. Note that the conclusion is an equality of projected sets, while the value equalities between `y` and `y'` as elements of the model are not claimed.
<!--zh-->
把对象语言的断言向外读，得到可用的结论。给定 `svAt f` 的满足关系，量词为模型的任意元素 `x`、`y`、`y'` 提供那条蕴含；把两条隶属 `Holds x y` 与 `Holds x y'` 各自先从外部形式传输到量词所期望的满足形式再喂入，便得到两个底层值相等的 `fst y ≡ fst y'`。注意结论是投影后集合的相等，而 `y` 与 `y'` 作为模型元素之间的相等并未被断言。
<!--ja-->
対象言語の主張を外へ読み出すと、使える結論が得られます。`svAt f` の充足が与えられれば、量化子は模型の任意の要素 `x`、`y`、`y'` に対してその含意を供給します。二つの所属 `Holds x y` と `Holds x y'` を、それぞれ外部の形から量化子が期待する充足の形へ輸送して渡せば、二つの底にある値の等式 `fst y ≡ fst y'` が得られます。結論が射影後の集合の等式であり、模型の要素としての `y` と `y'` の等式は主張されていないことに注意してください。
<!--/-->

```agda
        → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) zero)
        ≡ (pr (fst x) (fst y') ∈ fst (lookup f γ))
    at' x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) zero
                   (y' ∷ y ∷ x ∷ γ)

  svAt-out : ⟨ γ ⊨ svAt f ⟩
```

<!--en-->
The converse builds satisfaction rather than extracting it. A function taking any three elements with two agreeing memberships to the equality of their values is exactly what the three quantifiers and the two implications ask for; each expected membership proof is manufactured by transporting the external one forward along `at` or `at'`. Together the two lemmas say that satisfaction of `svAt f` and the external single-valuedness condition imply each other, though the statement keeps them as two functions rather than one packaged path.
<!--zh-->
逆向构造的是满足关系本身。一个从任意三个带两条隶属的元素到「其取值相等」的函数，恰是三个量词与两条蕴含所要求的东西；每个所需的隶属证明都由外部那条沿 `at` 或 `at'` 正向传输而造出。两条引理合起来说明：`svAt f` 的满足与外部的单值性条件相互蕴涵，只是陈述把二者保持为两个函数，而非打包成一条路径。
<!--ja-->
逆向きは充足を取り出すのではなく組み立てます。二つの所属が一致する任意の三つの要素を、それらの値の等しさへ送る関数は、三つの量化子と二つの含意が要求するものにちょうど等しく、必要な所属の証明はそれぞれ、外部のものを `at` か `at'` に沿って順方向へ輸送して作られます。二つの補題を合わせると、`svAt f` の充足と外部の一価性の条件は互いに従いますが、述べ方はそれらを二つの関数として保ち、一本のパスへはまとめていません。
<!--/-->

```agda
           → (x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y'
  svAt-out h x y y' p q = h x y y'
    (subst ⟨_⟩ (sym (at x y y')) p) (subst ⟨_⟩ (sym (at' x y y')) q)

  svAt-in : ((x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y')
          → ⟨ γ ⊨ svAt f ⟩
```

<!--en-->
The introduction direction `svAt-in` mirrors the extraction, with the transports pointing the other way: each external membership is carried forward along the adequacy path into the satisfaction the implications expect, and the three quantifiers then apply the function `h`. Both directions keep the whole statement at the level of underlying sets: the conclusion is an equality of the projected values `fst y` and `fst y'`, and the memberships supplied are about projected pairs. Nothing here asserts that every argument has a value, or that the graph is inhabited; those are separate questions settled by the domain condition.
<!--zh-->
引入方向 `svAt-in` 是消去的镜像，只是传输方向相反：每条外部隶属沿充分性路径正向传输为各蕴含所期望的满足形式，然后三个全称量词施用函数 `h`。两个方向都把整个陈述保持在底层集合的层面：结论是投影值 `fst y` 与 `fst y'` 的相等，所供给的隶属也针对投影后的对。这里没有断言每个论元都有取值，也没有断言图非空；那是下一节定义域条件的事。
<!--ja-->
導入の方向 `svAt-in` は除去の鏡像で、輸送の向きが逆です。外部の所属をそれぞれ妥当性の経路に沿って順方向へ、含意が期待する充足の形へ運び、三つの全称量化子が関数 `h` を適用します。どちらの方向でも、主張全体が底にある集合の水準に保たれます。結論は射影された値 `fst y` と `fst y'` の等しさであり、供給される所属も射影された対についてのものです。ここでは、すべての引数が値を持つことも、グラフが空でないことも主張しません。それは次節の定義域の条件に委ねられています。
<!--/-->

```agda
  svAt-in h x y y' p q = h x y y'
    (subst ⟨_⟩ (at x y y') p) (subst ⟨_⟩ (at' x y y') q)
```

<!--en-->
## The domain

The application reader already proved for the pair reader answers one question: does the pair of these two values belong to the graph? A graph can meet it at some arguments and miss at others, so the next structural property asks which arguments have entries at all. Being in the domain is simply having a value, and the reader for it is a single unbounded existential over the model. The domain condition then compares a candidate set `d` with the graph by saying that membership in `d` and having a value imply each other, stated as two implications because the object language has no biconditional of its own.

The three logical components developed so far, application, single-valuedness, and the exact domain, are independent of one another, and each is needed separately later: a graph can be single-valued yet miss arguments, defined exactly on `d` yet multi-valued, and so on. What the condition does not do is construct anything; it is a predicate that one candidate set either satisfies or fails. The two extraction lemmas are each used in one direction: `domAt-out` consumes an actual entry and yields domain membership, while `domAt-in` consumes domain membership and yields only the truncated existence of an entry, since from membership in the domain alone one merely knows that some entry exists. The introduction direction, needed when a set must be shown to satisfy the description from external evidence, carries a third name.
<!--zh-->
## 定义域

上一节的取值读式回答一个问题：这两个值组成的对属于该图吗？一个图可以在某些论元处命中、在另一些处落空，故下一个结构性质问的是：哪些论元有条目。落在定义域中就是有取值，其读式只是对模型的一次无界存在。定义域条件随后把候选集合 `d` 与图相比较，说「属于 `d`」与「有取值」互相蕴含；由于对象语言没有自带的双条件，这条陈述写成两条蕴含。

至此发展出的三个逻辑成分，取值、单值性与恰当定义域，彼此独立，且在后文中各自单独被用到：一个图可以单值却漏掉某些论元，可以恰定义在 `d` 上却多值，等等。这个条件并不构造任何东西；它是一个谓词，某个候选集合要么满足它要么不满足。两条消去引理各只用一个方向：`domAt-out`{.Agda} 消费一条实际的条目而得到定义域中的隶属，`domAt-in`{.Agda} 则消费定义域中的隶属，只得到条目的截断存在，因为仅凭定义域中的隶属，人们只知道某个条目存在。当需要从外部证据证明某个集合**满足**这条描述时所需的引入方向，另取了第三个名字。
<!--ja-->
## 定義域

前節の適用の読み式が答えるのは一つの問いです。この二つの値の対はグラフに属するか。グラフはある引数では命中し、別の引数では外れることがあるので、次の構造的性質は、どの引数が項目を持つのかを問います。定義域に属するとは値を持つことであり、その読み式は模型に対する無界の存在量化がひとつあれば足ります。定義域の条件は続いて、候補の集合 `d` とグラフを比べ、「`d` に属する」ことと「値を持つ」ことが互いに含意し合うと言います。対象言語には双条件が備わっていないため、これは二つの含意として述べられます。

ここまでに展開した三つの論理的成分、適用、一価性、ちょうどの定義域は互いに独立であり、後ではそれぞれが別々に使われます。グラフは一価でありながら引数を漏らすことも、`d` の上でちょうど定義されながら多値であることもできます。この条件が何かを構成するのではない点にも注意してください。これは述語であり、ある候補の集合がそれを満たすかどうかを判定するだけです。二つの除去の補題はそれぞれ一方向で使われます。`domAt-out`{.Agda} は実際の項目を消費して定義域への所属を与え、`domAt-in`{.Agda} は定義域への所属を消費して項目の切り詰められた存在だけを与えます。定義域への所属だけからは、ある項目が存在することしか分からないからです。ある集合が外部の証拠からこの記述を**充足**することを示すときに必要な導入の方向には、三つ目の名前が与えられます。
<!--/-->

<!--en-->
The definition is a single unbounded existential over the model: there merely exists a value `y` with the pair of the argument and `y` in the graph. The quantifier ranges over the carrier `S` of the model, not over a stage of the hierarchy, so the reader says exactly what it should. The adequacy statement unfolds the existential's satisfaction to the corresponding dependent sum; since `∃[ y ∶ S ] _` packages the existence of `y` propositionally, the right-hand side is itself truncated, asserting only that some such `y` exists.
<!--zh-->
定义是对模型的一次无界存在：仅仅存在取值 `y`，使论元与 `y` 的对属于该图。量词遍历的是模型的载体 `S`，而非层级的某一层，故读式所说的恰是它应当说的。充分性陈述把存在的满足关系展开为相应的依赖和；由于 `∃[ y ∶ S ] _` 以命题方式包装 `y` 的存在，右边本身也是截断的，只断言这样的 `y` 存在。
<!--ja-->
定義は模型に対する無界の存在量化がひとつです。引数と `y` の対がグラフに属するような値 `y` が、単に存在する、というものです。量化子が渡るのは階層のある段階ではなく模型の台 `S` なので、読み式は言うべきことをちょうど言います。妥当性の主張は存在量化の充足を対応する依存和へ展開します。`∃[ y ∶ S ] _` は `y` の存在を命題的に包装するため、右辺もそれ自体切り詰められており、そのような `y` の存在しか主張しません。
<!--/-->

```agda
inDomAt : ∀ {n} → Fin n → Fin n → Formula S n
inDomAt f x = ∃̇ (appAt (suc f) (suc x) zero)

inDomAt-adequate : ∀ {n} (f x : Fin n) (γ : S ^ n)
  → (γ ⊨ inDomAt f x)
  ≡ (∃[ y ∶ S ] (pr (fst (lookup x γ)) (fst y) ∈ fst (lookup f γ)))
```

<!--en-->
The proof needs no new argument: satisfaction of an unbounded existential is the join of its fibers, so the two sides agree pointwise at each `y`, and the pointwise agreement is one instance of the application adequacy at the extended environment. With having a value settled, the domain condition `domAt f d` compares a candidate set `d` with the graph in both directions: for every element `x`, membership of the projected `x` in `d` implies having a value, and having a value implies membership in `d`. The two implications are conjoined because the language supplies no symbol standing for their joint claim.
<!--zh-->
证明无需新的论证：无界存在的满足是其各纤维的析取，故两边在每个 `y` 处逐点一致，而逐点一致恰是扩展环境处取值充分性的一次实例。有取值一事定案后，定义域条件 `domAt f d` 在两个方向上把候选集合 `d` 与图比较：对每个元素 `x`，投影后的 `x` 属于 `d` 蕴含有取值，有取值又蕴涵属于 `d`。两条蕴含以合取相连，因为语言中没有符号直接表示它们共同的断言。
<!--ja-->
証明に新しい議論は要りません。無界な存在量化の充足はそのファイバーの選言なので、両辺は各 `y` で点的に一致し、その点的な一致こそ、拡張環境での適用の妥当性の実例です。値を持つことが確まったところで、定義域の条件 `domAt f d` は候補の集合 `d` をグラフと両方向に比べます。すべての要素 `x` に対し、射影された `x` の `d` への所属は値を持つことを含意し、値を持つことは `d` への所属を含意する、というものです。二つの含意が連言で結ばれるのは、言語がその共同の主張を表す記号を持たないからです。
<!--/-->

```agda
inDomAt-adequate f x γ =
  cong (⋁ S) (funExt (λ y → appAt-adequate (suc f) (suc x) zero (y ∷ γ)))

domAt : ∀ {n} → Fin n → Fin n → Formula S n
domAt f d = ∀̇ ( (inDomAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc d)))
             ∧̇ ((var zero ∈̇ var (suc d)) ⇒̇ inDomAt (suc f) zero) )
```

<!--en-->
The direction lemmas are stated for a fixed graph slot `f`, a fixed candidate `d`, and a fixed environment `γ`. The helper `step` fixes once and for all the adequacy path for the quantified body: at an element `x` of the model, satisfaction of the having-a-value formula is a path to the truncated existence of a `y` with the projected pair of `x` and `y` in the graph. Every transport below goes through this one path.
<!--zh-->
方向引理相对于固定的图槽位 `f`、固定的候选 `d` 与固定环境 `γ` 陈述。辅助命题 `step` 一劳永逸地固定被量化主体的充分性路径：在模型的元素 `x` 处，「有取值」公式的满足是一条通往「投影后的 `x` 与 `y` 的对属于图」的截断存在的路径。下面每一次传输都经过这条唯一的路径。
<!--ja-->
方向の補題は、固定されたグラフのスロット `f`、候補 `d`、環境 `γ` に対して述べられます。補助の `step` は、量化された本体の妥当性のパスを一度固定します。模型の要素 `x` において、「値を持つ」公式の充足は、射影された `x` と `y` の対がグラフに属するような `y` の切り詰められた存在へのパスです。以下の輸送はすべてこの一本のパスを通ります。
<!--/-->

```agda

module _ {n : ℕ} (f d : Fin n) (γ : S ^ n) where
  private
    step : (x : S)
         → ((x ∷ γ) ⊨ inDomAt (suc f) zero)
         ≡ (∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)))
```

<!--en-->
The extraction `domAt-out` consumes an entry and yields domain membership. Given an actual witness pair `x`, `y` with the membership `p`, the truncated form is assembled as `∣ y , p ∣₁`, transported backward through `step` into the satisfaction the quantifier expects, and fed to the first implication at `x`. The output is a plain membership proof of the projected `x` in the projected `d`, with no truncation left.
<!--zh-->
消去 `domAt-out` 从条目得到定义域中的隶属。给定实际的见证对 `x`、`y` 及隶属 `p`，先把截断形式组装为 `∣ y , p ∣₁`，沿 `step` 反向传输到量词所期望的满足形式，再在 `x` 处喂给第一条蕴含。输出是一条素净的隶属证明：投影后的 `x` 属于投影后的 `d`，不留任何截断。
<!--ja-->
除去の `domAt-out` は項目を消費して定義域への所属を与えます。実際の証人の対 `x`、`y` と所属 `p` が与えられれば、切り詰められた形は `∣ y , p ∣₁` として組み立てられ、`step` を逆向きに輸送されて量化子が期待する充足の形になり、`x` で最初の含意に渡されます。出力は、射影された `x` が射影された `d` に属するという、切り詰めのない素の所属の証明です。
<!--/-->

```agda
    step x = inDomAt-adequate (suc f) zero (x ∷ γ)

  domAt-out : ⟨ γ ⊨ domAt f d ⟩ → (x y : S)
            → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst x ∈ fst (lookup d γ) ⟩
  domAt-out h x y p = h x .fst (subst ⟨_⟩ (sym (step x)) ∣ y , p ∣₁)
```

<!--en-->
The extraction `domAt-in` runs the other way, and keeps the truncation. Domain membership `m` is fed to the second implication, whose conclusion is the satisfaction of the having-a-value formula; transporting forward through `step` turns it into the truncated dependent sum. That truncated form is the correct statement: from membership in the domain alone one merely knows that some entry exists, not which one.
<!--zh-->
消去 `domAt-in` 反向执行，并保留截断。定义域中的隶属 `m` 被喂给第二条蕴含，其结论正是「有取值」公式的满足；沿 `step` 正向传输后，它变成截断的依赖和。这个截断形式正是应有的陈述：仅凭定义域中的隶属，人们只知道某个条目存在，并不知道是哪一个。
<!--ja-->
除去の `domAt-in` は逆方向に進み、切り詰めを保ちます。定義域への所属 `m` は二つ目の含意に渡され、その結論は「値を持つ」公式の充足です。`step` に沿って順方向に輸送すると、切り詰められた依存和に変わります。この切り詰められた形こそ正しい主張です。定義域への所属だけからは、ある項目が存在することしか、どれであるかは分かりません。
<!--/-->

```agda

  domAt-in : ⟨ γ ⊨ domAt f d ⟩ → (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩
           → ∥ (Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩) ∥₁
  domAt-in h x m = subst ⟨_⟩ (step x) (h x .snd m)

  domAt-intro : ((x : S)
                 → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
```

<!--en-->
The introduction direction packages the two implications pointwise. The hypothesis asks, for each `x`, a pair of functions: one from the truncated existence of an entry to membership in `d`, and one back. Since the target propositions are propositions, consuming a truncated sum here is legitimate, and the transports through `step` in each component mirror those of the two extraction lemmas.
<!--zh-->
引入方向把两条蕴含逐点打包。假设要求：对每个 `x`，给出一对函数，一个从条目的截断存在到 `d` 中的隶属，一个反向。由于目标都是命题，此处消费截断和是合法的；每个分量中沿 `step` 的传输与两条消去引理互为镜像。
<!--ja-->
導入の方向は、二つの含意を点的に包装します。仮定は、各 `x` に対して関数の対を要求します。一方は項目の切り詰められた存在から `d` への所属へ、もう一方はその逆へ進むものです。対象がどちらも命題であるため、ここで切り詰められた和を消去するのは正当であり、各成分での `step` に沿う輸送は、二つの除去の補題と互いに鏡像です。
<!--/-->

```agda
                    → ⟨ fst x ∈ fst (lookup d γ) ⟩)
                 × (⟨ fst x ∈ fst (lookup d γ) ⟩
                    → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩))
              → ⟨ γ ⊨ domAt f d ⟩
  domAt-intro g x = (λ h → g x .fst (subst ⟨_⟩ (step x) h))
```

<!--en-->
The assembly is exactly the shape of the conjunction of implications under the universal quantifier: for each `x` a pair whose first component answers the first implication and whose second answers the second, each component adjusted by the transport in the direction its side requires. With this, a set claimed to be the domain can be certified to satisfy `domAt f d` from purely external evidence.
<!--zh-->
组装恰好是全称量词下蕴含合取的形状：对每个 `x` 给出一个对，第一分量回答第一条蕴含，第二分量回答第二条，各分量按其所在一侧所需的方向经传输调整。有了它，一个被声称是定义域的集合，就可以仅凭外部的证据被证明满足 `domAt f d`。
<!--ja-->
組み立ては、全称量化子の下での含意の連言の形そのものです。各 `x` に対して対が与えられ、第一成分は最初の含意に、第二成分は二つ目の含意に答え、各成分はその側が要求する向きの輸送で調整されます。これにより、定義域だと主張される集合を、外部の証拠だけから `domAt f d` を充足すると証明できます。
<!--/-->

```agda
                  , (λ m → subst ⟨_⟩ (sym (step x)) (g x .snd m))
```

<!--en-->
## The pair, inside the model

The adequacy statements so far have read formulas of the model outward, into ambient facts. The remaining task is the reverse: to build things inside the model whose projections are the ambient sets the readers talk about. Everything rests on one construction, the ordered pair of two elements of the model. It exists because the model has its own pairing operation, and applying it three times following the Kuratowski scheme produces an internal pair of any two elements, with no certificate to supply, since the pairing lands in the carrier by construction. What must be proved is that this internal pair projects to the ambient one: reading it through the underlying set gives exactly the hierarchy's pair of the projected components, with the singleton identity handling the component that appears twice.
<!--zh-->
## 模型内的配对

前面的充分性陈述都在把模型的公式向外读成周遭的事实。剩下的任务是反方向：在模型内部构造一些东西，使它们的投影正是那些读式所谈的周遭集合。一切都建立在一个构造之上：模型中两个元素的有序对。它之所以存在，是因为模型有自己的配对运算；沿 Kuratowski 方案把它应用三次，就得到任意两个元素的内部对，且无需提供任何证书，因为配对按构造就落在载体之中。必须证明的是这个内部对投影为周遭的对：沿底层集合读出它，恰得层级中两个投影分量的对，其中出现两次的那个分量由单点集恒等式处理。
<!--ja-->
## モデル内部の対

これまでの妥当性の主張は、模型の論理式を外へ読み出して周囲の事実へ変えるものでした。残りの課題はその逆です。読み式が語る周囲の集合が射影として現れるように、模型の内部で何かを作ること。すべては一つの構成、すなわち模型の二つの要素の順序対にかかっています。それが存在するのは、模型が自身の対の構成を持つからです。Kuratowski の方式に従ってこれを三度施せば、任意の二つの要素の内部対が得られ、証明書を補う必要はありません。対の構成は構成によって台に着地するからです。証明すべきは、この内部対が周囲の対へ射影されることです。底にある集合を通して読めば、射影された二つの成分の階層の対がちょうど得られ、二度現れる成分は単集合の等式が処理します。
<!--/-->

<!--en-->
The Kuratowski coding inside the model mirrors the ambient definition term by term: `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆` becomes `pairʟ` applied to `pairʟ a a` and `pairʟ a b`. Because `pairʟ` lands in the carrier `S` by construction, the result is an element of the model with no certificate to supply: each inner occurrence of `pairʟ` already carries its own constructibility internally, so composing them needs no additional proof.
<!--zh-->
模型内的 Kuratowski 编码逐项镜像环境定义：`pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆` 变成 `pairʟ` 作用于 `pairʟ a a` 与 `pairʟ a b`。由于 `pairʟ` 按构造落在载体 `S` 中，结果是模型的一个元素，无需再提供证书：每处内层的 `pairʟ` 已自带可构造性，故复合它们不需要任何额外证明。
<!--ja-->
モデル内部での Kuratowski 対の符号化は、周囲の定義を項ごとに写します。`pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆` は、`pairʟ a a` と `pairʟ a b` に `pairʟ` を施したものになります。`pairʟ` は構成によって台 `S` に着地するため、結果は証明書を補うことのないモデルの要素です。内側の `pairʟ` の各出現がすでに自身の構成可能性を担っているので、それらを重ね合わせるのに追加の証明は要りません。
<!--/-->

```agda
prʟ : S → S → S
prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)

prʟ-fst : (a b : S) → fst (prʟ a b) ≡ pr (fst a) (fst b)
prʟ-fst a b =
    pairʟ-fst (pairʟ a a) (pairʟ a b)
```

<!--en-->
The projection equation unfolds the same recursion in `V`. The outer projection gives the pair of the two projections; the first component projects to the unordered pair of `fst a` with itself, which the hierarchy's identity `pair-singleton` collapses to the singleton of `fst a`. The result is the promised identification: reading the model's pair through the underlying set yields exactly `pr (fst a) (fst b)`. This equation is the hinge of the next section, since every tag-and-pair code will be projected through it.
<!--zh-->
投影等式在 `V` 中展开同一递归。外层投影给出两个投影的对；第一分量投影为 `fst a` 与自身的无序对，而层级的恒等式 `pair-singleton` 把它塌缩为 `fst a` 的单点集。结果正是所允诺的等同：沿底层集合读出模型的对，恰好得到 `pr (fst a) (fst b)`。这条等式是下一节的关键，因为每个「标签加对」的码都将经由它投影。
<!--ja-->
射影の等式は、同じ再帰を `V` の中で展開します。外側の射影は二つの射影の対を与え、第一成分は `fst a` とそれ自身の非順序対へ射影され、階層の等式 `pair-singleton` がそれを `fst a` の単集合へ畳みます。得られるのは約束された同一視です。モデルの対を底にある集合を通して読めば、ちょうど `pr (fst a) (fst b)` が得られます。この等式が次節の要になります。タグと対から成るすべての符号がこれを通して射影されるからです。
<!--/-->

```agda
  ∙ cong₂ ⁅_,_⁆ (pairʟ-fst a a ∙ pair-singleton (fst a)) (pairʟ-fst a b)
```

<!--en-->
## The coding, at the model

The pair `prʟ` and the numerals are injective, which is what the generic coding scheme asks of a structure, so terms and formulas now code into `L` itself. Two facts follow. A code is an element of the model **by construction**, with no constructibility certificate to supply; and distinct expressions have distinct codes, which is what a table indexed by codes needs, since two different subformula occurrences must not share a key.

The bridge then compares the two codings. Internal pairing and numerals project to their ambient counterparts, so every code, being built from tags pairing a numeral with a payload, projects to the ambient code of the formula whose constants have been projected by `fst`. This is what lets the adequacy theorems proved on the hierarchy side be applied to codes built inside the model.
<!--zh-->
## 模型处的符号化

对 `prʟ` 与诸数码是单射的，而这是一般编码方案对结构的全部要求，故词项与公式如今可编码进 `L` 自身。由此得到两件事实。其一，一个码**按构造**就是模型的元素，无需可构造性证书；其二，不同的表达式有不同的码，这正是「以码为索引的表」所需要的：两处不同的子公式的出现不可共用同一个键。

随后，桥把两套编码加以比较。内部的对与数码投影为周遭的对应物，而每个码都由「标签把数码与载荷配对」造出，故每个码都投影为那条常元已被 `fst` 投影的公式的周遭码。正是这一点使在层级一侧证明的充分性定理，能够施于造在模型内部的诸码。
<!--ja-->
## モデルにおける符号化

対 `prʟ` と数項は単射であり、これは一般的な符号化の仕組みが構造に求める条件のすべてなので、項と論理式は `L` 自身の中へ符号化できます。ここから二つの事実が従います。第一に、符号は**構成によって**モデルの要素であり、構成可能性の証明書を補う必要がありません。第二に、異なる式は異なる符号を持つことで、これは符号を鍵とする表に必要な性質です。異なる部分式の出現が同じ鍵を共有してはならないからです。

続いて、橋渡しが二つの符号化を比較します。内部の対と数項は周囲の対応物へ射影され、すべての符号はタグが数項と本体を対にする形で組み立てられているので、各符号は定数を `fst` で射影した論理式の周囲の符号へと射影されます。階層の側で証明された妥当性の定理を、モデルの内部で作られた符号に適用できるのはこのためです。
<!--/-->

<!--en-->
Injectivity of `prʟ` follows the same route as its projection: if the pairs of model elements are equal, projecting both sides along `prʟ-fst` gives equality of the ambient pairs, and the ambient injectivity `pr-inj` recovers equality of the projected components. Each component equality lives in a dependent sum whose second component is a proposition, namely the certificate `isL`, so `Σ≡Prop` licenses concluding the full equality of the model elements from the equality of their first components.
<!--zh-->
`prʟ` 的单射性沿其投影的同一路线：若两个模型元素的对相等，沿 `prʟ-fst` 投影两侧便得到周遭对相等的路径，而周遭的单射性 `pr-inj` 取回两个投影分量的相等。每个分量的相等生活在一个依赖和中，其第二分量是命题，即证书 `isL`，故 `Σ≡Prop` 允许从第一分量的相等得出模型元素整体的相等。
<!--ja-->
`prʟ` の単射性は、その射影と同じ道をたどります。モデルの要素の対が等しければ、両辺を `prʟ-fst` に沿って射影することで周囲の対の等しさが得られ、周囲の単射性 `pr-inj` が射影された成分の等しさを取り戻します。各成分の等しさは、第二成分が命題、すなわち証明書 `isL` である依存和の中に住むので、`Σ≡Prop` によって、第一成分の等しさからモデルの要素全体の等しさを結論できます。
<!--/-->

```agda
prʟ-inj : {a b c d : S} → prʟ a b ≡ prʟ c d → (a ≡ c) × (b ≡ d)
prʟ-inj {a} {b} {c} {d} e =
    Σ≡Prop (λ v → snd (isL v)) (pr-inj q .fst)
  , Σ≡Prop (λ v → snd (isL v)) (pr-inj q .snd)
  where
```

<!--en-->
The path of ambient pair equalities is assembled from the three available equations: reverse the projection of the left pair, apply the assumed equality under `fst`, and project the right pair. The same pattern gives injectivity of the numerals, where `numeralL-fst` plays the projection role and `#-inj′` recovers equality of the natural number indices from equality of the projected finite ordinals.
<!--zh-->
周遭对相等的那条路径由三条已有等式组装而成：取左对的投影之逆，在 `fst` 之下施加所设的相等，再投影右对。同一模式给出数码的单射性，只是 `numeralL-fst` 扮演投影的角色，而 `#-inj′` 从投影后的有限序数的相等取回自然数下标的相等。
<!--ja-->
周囲の対の等しさのパスは、手もとの三つの等式から組み立てます。左の対の射影を逆向きにたどり、仮定の等しさを `fst` の下で施し、右の対を射影します。同じ型が数項の単射性も与えます。ここでは `numeralL-fst` が射影の役を務め、`#-inj′` が射影された有限順序数の等しさから自然数の添字の等しさを取り戻します。
<!--/-->

```agda
  q : pr (fst a) (fst b) ≡ pr (fst c) (fst d)
  q = sym (prʟ-fst a b) ∙ cong fst e ∙ prʟ-fst c d

numeralL-inj : {j k : ℕ} → numeralL j ≡ numeralL k → j ≡ k
numeralL-inj {j} {k} e =
  #-inj′ (sym (numeralL-fst j) ∙ cong fst e ∙ numeralL-fst k)
```

<!--en-->
With the two injectivities in hand, the generic coding scheme instantiates at the structure `𝒮ʟ` with `prʟ` and `numeralL` as its pairing and numerals: the resulting module `LCode` codes terms and formulas into the carrier `S`. The bridge lemmas then relate the two codings, and the basic case is already visible in `tagBridge`: a tag pairs a numeral with a payload, so its projection is the ambient tag of the projected payload, by `prʟ-fst` and the projection equation of the numeral.
<!--zh-->
两条单射性到手后，一般编码方案在结构 `𝒮ʟ` 处实例化，以 `prʟ` 为配对、`numeralL` 为数码：所得模块 `LCode` 把词项与公式编码进载体 `S`。桥引理接着联系两套编码，而基本情形在 `tagBridge` 中已经可见：标签把一个数码与一个载荷配成对，故其投影由 `prʟ-fst` 与数码的投影等式给出「投影后载荷」的环境标签。
<!--ja-->
二つの単射性が揃うと、一般的な符号化の仕組みが構造 `𝒮ʟ` で実例化されます。`prʟ` を対に、`numeralL` を数項に取ると、得られるモジュール `LCode` が項と論理式を台 `S` の中へ符号化します。橋渡しの補題は続いて二つの符号化を結びます。基本の場合はすでに `tagBridge` に見えます。タグは数項と本体を対にするので、その射影は `prʟ-fst` と数項の射影等式により、射影された本体の周囲のタグになります。
<!--/-->

```agda

module LCode = FOL.Coding {ℓ-suc ℓ} 𝒮ʟ prʟ prʟ-inj numeralL numeralL-inj

tagBridge : (k : ℕ) (x : S) → fst (LCode.mkTag k x) ≡ VCode.mkTag k (fst x)
tagBridge k x = prʟ-fst (numeralL k) x ∙ cong₂ pr (numeralL-fst k) refl

codeBridgeTm : ∀ {n} (t : Term S n) → fst LCode.⌜ t ⌝ᵗ ≡ VCode.⌜ mapTm fst t ⌝ᵗ
codeBridgeTm (con c) = tagBridge 0 c
```

<!--en-->
For terms the recursion has two cases. A constant is coded as the tag 0 applied to itself, so the bridge is `tagBridge 0` at that constant. A variable is coded as the tag 1 applied to the numeral of its index, and the extra congruence step moves the projection equation of that numeral under the tag, since `mapTm fst` has replaced the variable constant by its projection. The formula recursion starts the same way: membership pairs its two terms, with the tag 0 here marking the membership constructor of the ambient coding, and the payload path is `prʟ-fst` followed by congruence over the two term bridges.
<!--zh-->
词项的递归只有两种情形。常元被编码为标签 0 作用于其自身，故桥就是在该常元处的 `tagBridge 0`。变元被编码为标签 1 作用于其下标的数码，而额外那步同余把该数码的投影等式移到标签之下，因为 `mapTm fst` 已把变元常元换成它的投影。公式的递归同样开头：隶属把两个词项配成对，这里的标签 0 标记环境编码中的隶属构造子，载荷路径是 `prʟ-fst` 再接对两条词项桥的同余。
<!--ja-->
項の再帰には二つの場合しかありません。定数はタグ 0 をそれ自身に施したものとして符号化されるので、橋はその定数での `tagBridge 0` です。変数はタグ 1 をその添字の数項に施したものとして符号化され、追加の合同の段階が、数項の射影等式をタグの下へ移します。`mapTm fst` が変数の定数をその射影に置き換えたからです。論理式の再帰も同じように始まります。所属は二つの項を対にし、ここでのタグ 0 は周囲の符号化における所属の構成子を示し、本体のパスは `prʟ-fst` に二つの項の橋に対する合同が続きます。
<!--/-->

```agda
codeBridgeTm (var i) =
  tagBridge 1 (numeralL (toℕ i)) ∙ cong (VCode.mkTag 1) (numeralL-fst (toℕ i))

codeBridge : ∀ {n} (φ : Formula S n) → fst LCode.⌜ φ ⌝ ≡ VCode.⌜ mapFo fst φ ⌝
codeBridge (t ∈̇ u) = tagBridge 0 _ ∙ cong (VCode.mkTag 0)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
```

<!--en-->
The remaining binary constructors repeat one pattern. Each is marked by its own tag, the payload is the ordered pair of the codes of the two immediate subformulas, and the projection path is one tag equation composed with congruence over the pair of the two recursive bridges. Equality, conjunction, disjunction, and implication differ only in the tag number and in which subformula bridge is applied where.
<!--zh-->
余下的二元构造子重复同一个模式。每个构造子由自己的标签标记，载荷是两条直接子公式之码的有序对，投影路径则是一条标签等式再复合对两条递归桥的同余。相等、合取、析取与蕴涵只在标签数字以及两条子桥各自用在哪里上不同。
<!--ja-->
残りの二項の構成子は一つの型を繰り返します。各構成子は固有のタグで示され、本体は二つの直接の部分式の符号の順序対であり、射影のパスはタグの等式に、二つの再帰的な橋の対に対する合同を複合したものです。等号、連言、選言、含意が異なるのは、タグの番号と、二つの橋をどちらに施すかだけです。
<!--/-->

```agda
codeBridge (t ≐ u) = tagBridge 1 _ ∙ cong (VCode.mkTag 1)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
codeBridge (a ∧̇ b) = tagBridge 2 _ ∙ cong (VCode.mkTag 2)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ∨̇ b) = tagBridge 3 _ ∙ cong (VCode.mkTag 3)
```

<!--en-->
The nullary and unary constructors fit the same frame with degenerate payloads. Falsity is coded as the tag 5 applied to the numeral of zero, so its bridge is one tag equation with the numeral projection inside. The unbounded quantifiers carry a single subformula, so no pairing occurs and the payload path is just the recursive bridge of the body, transported under the tag.
<!--zh-->
零元与一元构造子以退化的载荷嵌入同一个框架。永假式被编码为标签 5 作用于零的数码，故其桥是一条标签等式，内嵌数码的投影。无界量词只携带一条子公式，因而不发生配对，载荷路径就是主体的递归桥，在标签之下传输。
<!--ja-->
零項と一項の構成子も、退化した本体で同じ枠組みに収まります。恒偽はタグ 5 をゼロの数項に施したものとして符号化されるので、その橋は数項の射影を内に含むタグの等式一本です。非有界の量化子は部分式を一つしか担わないため、対は現れず、本体のパスはその部分式の再帰的な橋をタグの下で輸送したものです。
<!--/-->

```agda
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ⇒̇ b) = tagBridge 4 _ ∙ cong (VCode.mkTag 4)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge ⊥̇       = tagBridge 5 _ ∙ cong (VCode.mkTag 5) (numeralL-fst 0)
codeBridge (∃̇ a)   = tagBridge 6 _ ∙ cong (VCode.mkTag 6) (codeBridge a)
```

<!--en-->
The bounded quantifiers are the only constructors mixing both levels: a bounded quantifier pairs a term with a formula, so the payload path projects the outer pair and then applies the term bridge and the formula bridge to the two components. With this, the recursion covers every constructor of terms and formulas, and every internal code is known to project to the ambient code of the projected formula.
<!--zh-->
有界量词是唯一同时涉及两个层面的构造子：有界量词把一个词项与一条公式配对，故载荷路径先投影外层对，再把词项桥与公式桥分别施于两个分量。至此，递归覆盖词项与公式的每个构造子，且每个内部码都已知投影为投影后公式的周遭码。
<!--ja-->
有界量化子は、両方の水準に関わる唯一の構成子です。有界量化子は項と論理式を対にするので、本体のパスは外側の対を射影した後、項の橋と論理式の橋をそれぞれの成分に施します。これで再帰は項と論理式のすべての構成子を扱い尽くし、すべての内部の符号が、射影された論理式の周囲の符号へ射影されることが分かりました。
<!--/-->

```agda
codeBridge (∀̇ a)   = tagBridge 7 _ ∙ cong (VCode.mkTag 7) (codeBridge a)
codeBridge (∀̇∈ t a) = tagBridge 8 _ ∙ cong (VCode.mkTag 8)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))
codeBridge (∃̇∈ t a) = tagBridge 9 _ ∙ cong (VCode.mkTag 9)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))

```

<!--en-->
## Environments

An environment over a set B is a function whose values all lie in B, so a candidate set e qualifies as one exactly when four things hold at once: it is single-valued, its domain is the given set d, its values lie in B, and it is *made of pairs*. The four clauses are logically independent, and each earns its place. Single-valuedness constrains only arguments that appear twice; the domain clause says that the arguments with entries are exactly the members of d; the value restriction says that every value lies in B. The first three speak only about members of e that are ordered pairs, so a set carrying additional non-pair elements would still pass all of them. The fourth conjunct closes this by requiring every member of e to be a pair of a member of d and a member of B, which makes each environment a subset of d × B; that exclusion of non-pair members is what the first three cannot supply.

What this section provides is a predicate on a single candidate, together with extraction lemmas that read each conjunct back out. Whether some particular set *is* the set of all environments of a given length is a different and harder question, not settled here.
<!--zh-->
## 环境

给定集合 B 之上的环境是一个取值都落在 B 中的函数，因此一个候选集合 e 恰在以下四条同时成立时才算一个：它是单值的；它的定义域是给定的 d；它的取值落在 B 中；而且它**由诸对构成**。这四条在逻辑上各自独立，各有其用。单值性只约束重复出现的论元；定义域一条说有对出现的论元恰是 d 的成员；取值限制说每个取值都落在 B 中。前三条只谈及 e 中那些是有序对的成员，所以一个另带非对元素的集合也能通过它们。第四条合取项弥补了这一点，它要求 e 的每个成员都是「d 的一个成员与 B 的一个成员」的对，从而使每个环境都是 d × B 的子集；排除非对成员这件事，正是前三条无法给出的。

本节给出的是关于单个候选的谓词，以及把每个合取项读回出来的消去引理。某个特定集合**是否就是**给定长度的全体环境的集合，是另一个更难的问题，这里不作解决。
<!--ja-->
## 環境

集合 B の上の環境とは、その値がすべて B に入る関数のことです。したがって候補集合 e が環境であるのは、次の四つが同時に成り立つとき、そのときに限ります。e が一価であること、定義域が与えられた d であること、値が B に入ること、そして e が**順序対からできている**ことです。四つの条項は論理的に独立しており、それぞれに役割があります。一価性は二度現れる引数だけを制約し、定義域の条項は項目を持つ引数が d の要素にちょうど一致することを言い、値の制限はすべての値が B に入ることを言います。最初の三つは順序対であるような e の要素についてしか語らないので、対でない要素を余分に持つ集合でも通ってしまいます。第四の連言がこれを塞ぎます。e のすべての要素が「d の要素と B の要素の対」であることを要求し、各環境を d × B の部分集合にします。対でない要素の排除は、最初の三つからは得られないものです。

本節が与えるのは、一つの候補についての述語と、各連言を読み出す消去補題です。特定の集合がある長さの環境の全体の集合である**かどうか**は、別の、しかもより難しい問題であり、ここでは扱いません。
<!--/-->

<!--en-->
The third conjunct restricts the values. Its statement quantifies over two variables x and y and says: whenever the pair of x and y belongs to the graph e, the value y must belong to B. Note what is *not* said: nothing requires any particular x to have a value at all, that is the separate domain clause. The clause constrains only existing entries, so it neither makes the graph a function nor fixes its domain.
<!--zh-->
第三个合取项限制取值。它对两个变元 x 与 y 作全称量化并断言：只要 x 与 y 构成的对属于图 e，取值 y 就必须属于 B。注意这里**没有**说什么：它不要求任何特定的 x 有取值，那是定义域一条的事。这一条只约束已有的条目，因此它既不使图成为函数，也不固定其定义域。
<!--ja-->
第三の連言は値の範囲を制限します。二つの変数 x と y について全称量化し、x と y の対がグラフ e に属するなら、値 y は B に属さねばならないと述べます。何が述べられて**いない**かにも注意してください。特定の x が値を持つことは要求せず、それは別の定義域の条項の仕事です。この条項はすでにある項目だけを制約するので、グラフを関数にするわけでも、その定義域を固定するわけでもありません。
<!--/-->

```agda
valuesInAt : ∀ {n} → Fin n → Fin n → Formula S n
valuesInAt f B = ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
                     ⇒̇ (var zero ∈̇ var (suc (suc B))) ))

valuesInAt-out : ∀ {n} (f B : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ valuesInAt f B ⟩ → (x y : S)
```

<!--en-->
Reading the clause out is one direction, and it is direct. Given a pair with first component x and value y in the graph, apply the universal quantifiers at x and y; the remaining obligation is the implication inside. The membership fact p is first converted into a satisfaction of the antecedent, which `appAt-adequate` identifies with membership at the projected environment (y ∷ x ∷ γ), so transporting along the symmetric equation supplies exactly the argument the quantified body demands. The conclusion is membership of the projected value in the projected B, no truncation involved anywhere.
<!--zh-->
把这一条读出来只需一个方向，而且是直接的。设图中已有以 x 为第一分量、以 y 为取值的对；把全称量词施加于 x 与 y 即可，剩下的待证事项就是其中的蕴含。故先把隶属事实 p 换成前件的满足：`appAt-adequate` 把该满足等同于在投影后的环境 (y ∷ x ∷ γ) 处的隶属，沿其对称等式作替换，便恰好给出量化主体所需要的论据。结论是投影后的取值属于投影后的 B，全程不涉及截断。
<!--ja-->
この条項を読み出すのは一方向だけで、しかも直接です。第一成分 x、値 y となる対がグラフにあれば、全称量化子を x と y に適用し、残る課題は内側の含意です。まず所属の事実 p を前件の充足へ変換します。`appAt-adequate` はその充足を、射影した環境 (y ∷ x ∷ γ) での所属と同一視するので、その対称な等式に沿って輸送すれば、量化された本体が要求する論拠がちょうど得られます。結論は射影した値の射影した B への所属であり、至る所で截断は現れません。
<!--/-->

```agda
               → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
               → ⟨ fst y ∈ fst (lookup B γ) ⟩
valuesInAt-out f B γ h x y p = h x y
  (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ))) p)

pairsInAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
```

<!--en-->
The fourth conjunct, the pairs clause, is written with bounded quantifiers alone. It says: for every member s of e there is a member u of d and a member v of B with s equal to the pair of u and v. Because the quantifiers range over actual members, the clause constrains only what already lies in the sets e, d and B, and its meaning will be read off those sets after projection. The body is the pair reader `prAtL` from earlier in this chapter, at indices shifted by the three binders.
<!--zh-->
第四个合取项，即诸对那条，全部用有界量词写出。它说：对 e 的每个成员 s，存在 d 的成员 u 与 B 的成员 v，使 s 等于 u 与 v 的对。由于量词遍历的是实际成员，这条只约束 e、d、B 中已有的东西，其含义也将在投影后从这些集合读出。主体是本章前文的对读式 `prAtL`，下标按三个约束子后移。
<!--ja-->
第四の連言、すなわち対の条項は、有界量化子だけで書かれています。e のすべての要素 s に対し、d の要素 u と B の要素 v で、s が u と v の対に等しいものが存在する、と述べるのです。量化子が実際の要素を動くので、この条項は e、d、B にすでにあるものだけを制約し、その意味は射影後にこれらの集合から読み出されます。本体は本章の前で与えた対の読み式 `prAtL` で、添字は三つの束縛子ぶんだけ後ろへずれます。
<!--/-->

```agda
pairsInAt e d B =
  ∀̇∈ (var e) (∃̇∈ (var (suc d)) (∃̇∈ (var (suc (suc B)))
    (prAtL (suc (suc zero)) (suc zero) zero)))

pairsIn-out : ∀ {n} (e d B : Fin n) (γ : S ^ n) → ⟨ γ ⊨ pairsInAt e d B ⟩
            → (s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
```

<!--en-->
The extraction from the pairs clause keeps the shape of satisfaction: the conclusion is a propositional truncation, merely asserting that such u and v exist. The hypothesis h is an ordinary proof that the formula holds, and s∈ is an ordinary membership of the projected s in the projected e. The type says precisely what is recovered: u in d, v in B, and the underlying set of s equal to the pair of their underlying sets, all merely.
<!--zh-->
从诸对那条读出时保留了满足的形状：结论是一个命题截断，只是**仅仅存在**这样的 u 与 v。前提 h 是「公式成立」的普通证明，而 s∈ 是投影后的 s 属于投影后的 e 的普通隶属。该类型准确说明能恢复什么：u 在 d 中、v 在 B 中，且 s 的底集等于二者底集的对，一切都仅仅是存在。
<!--ja-->
対の条項からの抽出は充足の形を保ちます。結論は命題的截断であり、そのような u と v が単に存在することしか主張しません。前提 h は「公式が成り立つ」ことの截断された証明であり、s∈ は射影した s の射影した e への普通の所属です。この型は、何が取り出せるかを正確に述べます。u が d に属し、v が B に属し、s の底集合がそれらの底集合の対に等しいこと、すべて単に存在するとしてです。
<!--/-->

```agda
            → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                  (⟨ fst u ∈ fst (lookup d γ) ⟩
                   × (⟨ fst v ∈ fst (lookup B γ) ⟩
                      × (fst s ≡ pr (fst u) (fst v)))))) ∥₁
pairsIn-out e d B γ h s s∈ = PT.rec squash₁
```

<!--en-->
The proof peels the two bounded existentials inside the truncation. Elimination of propositional truncation is legitimate here because the target is again a proposition, the truncation of a Sigma type, so nothing is chosen globally: each branch transforms its own witnesses. The inner step is the same transport seen throughout this chapter: `prAtL-adequate` turns the body's satisfaction into the path `fst s ≡ pr (fst u) (fst v)`, with the environment extended by v, u, s in binder order.
<!--zh-->
证明在截断之内剥去两层有界存在。这里消去命题截断是合法的，因为目标仍是命题，即一个 Σ 型的截断；所以并未全局地选取任何东西，每个分支只变换自己的见证。内层一步是本章反复出现的同一替换：`prAtL-adequate` 把主体的满足变成路径 `fst s ≡ pr (fst u) (fst v)`，环境按约束子的次序扩展为 v、u、s。
<!--ja-->
証明は、截断の内側で二つの有界存在を剥がします。命題的截断の消去がここで正当なのは、目標が再び命題、すなわち Σ 型の截断だからです。したがって何かを大域的に選ぶのではなく、各分岐が自分の証拠を変換するだけです。内側の一歩は本章で繰り返し現れたのと同じ輸送です。`prAtL-adequate` が本体の充足を経路 `fst s ≡ pr (fst u) (fst v)` に変え、環境は束縛子の順に v、u、s を加えて伸ばします。
<!--/-->

```agda
  (λ { (u , (u∈ , hv)) → PT.map
    (λ { (v , (v∈ , hp)) → u , (v , (u∈ , (v∈ , subst ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ)) hp))) })
    hv })
  (h s s∈)
```

<!--en-->
The reverse direction takes the per-member statement as a hypothesis. For every s whose projection lies in the projected e, the hypothesis merely supplies a truncated quadruple: u and v, their memberships, and the pair equation; the task is to turn that into satisfaction of the bounded formula. The two directions are kept as separate lemmas rather than merged into a path, because later arguments use exactly one direction at a time.
<!--zh-->
反方向把逐成员的陈述取为前提。对每个投影后属于投影后 e 的 s，前提仅仅提供被截断的四元组：u、v、二者各自的隶属，以及对的等式；任务是把它们变成有界公式的满足。两个方向保持为两条引理而不合并成一条路径，因为有关论证每次恰好只用一个方向。
<!--ja-->
逆向きは、要素ごとの主張を前提として取ります。射影した s が射影した e に属するすべての s に対し、前提が与えるのは截断された四つ組、すなわち u と v とそれぞれの所属および対の等式の単なる存在であり、課題はそれを有界公式の充足へ変えることです。両方向は一つの経路に併合されず、別々の補題として保たれます。後の議論は毎回どちらか一方向しか使わないからです。
<!--/-->

```agda

pairsIn-in : ∀ {n} (e d B : Fin n) (γ : S ^ n)
           → ((s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
              → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                    (⟨ fst u ∈ fst (lookup d γ) ⟩
                     × (⟨ fst v ∈ fst (lookup B γ) ⟩
```

<!--en-->
The construction transforms the truncated data of the hypothesis directly into satisfaction of the formula. The witnesses u and v pass through with their memberships, and the pair equation eq is carried to the body's satisfaction by transporting along the symmetry of the adequacy path, since here one travels from the set-level pair equation back to the reader's satisfaction. Truncation enters only through `PT.map`, which rebuilds the truncated sum around the rearranged data; the formula's own meaning supplies whatever truncation its quantifiers carry.
<!--zh-->
构造把前提中的被截断数据直接变成公式的满足。见证 u 与 v 连同各自的隶属原样通过，而对等式 eq 则沿充分性路径的对称等式传输，变成主体的满足，因为这里是从集合层面的对等式走回读式的满足。截断只经由 `PT.map` 进入，它在重新整理的数据周围重建被截断的和；公式自身的含义会供给其量词所需的任何截断。
<!--ja-->
構成は、前提の截断されたデータを公式の充足へ直接変換します。証拠 u と v はそれぞれの所属とともにそのまま通り、対の等式 eq は妥当性の経路の対称な等式に沿って輸送され、本体の充足になります。ここでは集合レベルの対の等式から読み式の充足へ戻るからです。截断は `PT.map` を通してのみ現れ、並べ直したデータの周りに截断された和を組み立て直します。公式自身の意味が、その量化子の担う截断を供給します。
<!--/-->

```agda
                        × (fst s ≡ pr (fst u) (fst v)))))) ∥₁)
           → ⟨ γ ⊨ pairsInAt e d B ⟩
pairsIn-in e d B γ k s s∈ = PT.map
  (λ { (u , (v , (u∈ , (v∈ , eq)))) → u , (u∈ , ∣ v , (v∈ , subst ⟨_⟩
    (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ))) eq) ∣₁) })
```

<!--en-->
Assembling the four clauses gives the definition of being an environment over d with values in B: single-valuedness, the exact domain, the value restriction, and the pairs clause, conjoined with `∧̇`. An anonymous module then fixes the arity, the three indices, an environment γ, and a proof that γ satisfies the conjunction, so the four projections can be stated once and used without repeating these parameters.
<!--zh-->
把四条合在一起，便得到「以 d 为定义域、取值在 B 中的环境」的定义：单值性、恰当的定义域、取值限制与诸对条目，用 `∧̇` 连接。接着一个匿名模块固定元数、三个指标、环境 γ，以及「γ 满足该合取」的证明，使四个投影可以只陈述一次，而不必每次重复这些参数。
<!--ja-->
四つの条項を組み合わせると、定義域 d、値の範囲 B の環境であることの定義が得られます。一価性、ちょうどの定義域、値の制限、そして対の条項を `∧̇` で連言したものです。続く無名モジュールはアリティ、三つの添字、環境 γ、および「γ がこの連言を充足する」ことの截断された証明を固定し、四つの射影を一度だけ述べて再利用できるようにします。
<!--/-->

```agda
  (k s s∈)

envOverAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envOverAt e d B =
  svAt e ∧̇ (domAt e d ∧̇ (valuesInAt e B ∧̇ pairsInAt e d B))

module _ {n : ℕ} (e d B : Fin n) (γ : S ^ n) (h : ⟨ γ ⊨ envOverAt e d B ⟩) where
```

<!--en-->
Each projection is just the corresponding component of the nested pair that the satisfaction of a fourfold conjunction is. The first is single-valuedness of e, the second the domain clause relating e and d, the third the value restriction toward B, and the fourth the pairs clause itself. With these in hand, an argument that needs only one aspect of environment-hood can take it without rebuilding the conjunction, and an argument that constructs an environment can be checked conjunct by conjunct.
<!--zh-->
每个投影就是四重连言的满足所构成的嵌套对中的相应分量。第一个是 e 的单值性，第二个是联系 e 与 d 的定义域条，第三个是朝向 B 的取值限制，第四个是诸对条目本身。四者齐备之后，只需环境性质的某一面的论证便可直接取用而无需重组整个合取；而构造环境的论证也可以逐条合取项来检验。
<!--ja-->
各射影は、四重連言の充足が作る入れ子の対の、対応する成分にほかなりません。第一は e の一価性、第二は e と d を結ぶ定義域の条項、第三は B への値の制限、第四は対の条項そのものです。四つがそろえば、環境であることの一面だけを必要とする議論は、連言を組み立て直さずにそれを取り出せます。環境を構成する議論も、連言を一項ずつ検査できます。
<!--/-->

```agda
  envOver-sv     : ⟨ γ ⊨ svAt e ⟩
  envOver-sv     = h .fst
  envOver-dom    : ⟨ γ ⊨ domAt e d ⟩
  envOver-dom    = h .snd .fst
  envOver-values : ⟨ γ ⊨ valuesInAt e B ⟩
```

<!--en-->
The four projections also expose why the definition is modular: uniqueness, domain, range, and pair shape can be transported or used independently, while their conjunction remains the single assertion that the candidate is an environment over `d` into `B`.
<!--zh-->
这四个投影也说明了定义的模块性：唯一性、定义域、取值范围与对的形状可以分别迁移或使用，而它们的合取仍是「该候选者为 `d` 上取值于 `B` 的环境」这一完整断言。
<!--ja-->
四つの射影は定義の分解可能性も示します。一意性、定義域、値域、対の形は別々に移したり利用したりでき、その連言は候補が `d` 上で `B` に値をとる環境だという一つの主張を保ちます。
<!--/-->

```agda
  envOver-values = h .snd .snd .fst
  envOver-pairs  : ⟨ γ ⊨ pairsInAt e d B ⟩
  envOver-pairs  = h .snd .snd .snd
```

<!--en-->
Every reader built so far inspects only the underlying sets that the assignment places at its indices: a satisfaction claim about a graph, a domain, or a value set is always stated after projecting the looked-up entries by `fst`. It follows that the description of an environment depends extensionally on just three sets, the projected graph, the projected domain, and the projected value set, and on nothing else about the assignment. So if two assignments, possibly of different arities, place the same three sets at the indices the description consults, the description holds at one exactly when it holds at the other.

This is what will later let a statement about an assignment be turned into a statement about a set that a construction actually built: the construction is free to present its environments through any indexing it likes, and as long as the three underlying sets match, the description carries over unchanged.
<!--zh-->
迄今构造的每条读式都只查看环境放在其指标处的底层集合：关于图、定义域或取值集合的满足断言，总是在用 `fst` 投影所查各项之后陈述的。由此可见，环境的描述在外延上只依赖三个集合，即投影后的图、投影后的定义域与投影后的取值集合，而不依赖环境的任何其他方面。于是，若两个元数可以不同的环境，把同样三个集合放在描述所查的指标处，则该描述在其中一个处成立，当且仅当它在另一个处成立。

这正是后文把「关于某个环境的陈述」变成「关于某个构造真正造出的集合的陈述」的关键：构造可以随意用它喜欢的索引来呈现其环境，只要三个底层集合吻合，描述便原样适用。
<!--ja-->
これまでに組み立てた読み式はどれも、割り当てがその添字に置いた底にある集合だけを見ます。グラフ、定義域、値の集合についての充足の主張は、常に検表した項目を `fst` で射影してから述べられます。したがって環境の記述は、射影されたグラフ、射影された定義域、射影された値の集合という三つの集合に外延的に依存するだけで、割り当てのそれ以外の側面には依存しません。アリティの異なりうる二つの割り当てが、記述が参照する添字に同じ三つの集合を置くなら、記述は一方で成り立つときちょうど他方でも成り立ちます。

これが後に「ある割り当てについての主張」を「構成が実際に作った集合についての主張」へ変える仕組みです。構成は好きな添字づけで環境を提示してよく、三つの底集合が一致する限り、記述はそのまま通用します。
<!--/-->

<!--en-->
The transfer theorem needs the introduction direction of the value restriction, the direction not extracted earlier: from the statement about every pair in the graph, back to a satisfaction. Given a function sending any pair in the graph to a value in B, the two universal quantifiers are applied, and the membership fact is converted into a satisfaction of the antecedent by the adequacy equation of the application reader. With this, both directions of `valuesInAt` are available as lemmas, one each.
<!--zh-->
迁移定理需要取值限制的引入方向，即此前未曾提取的那个方向：从「图中每个对如何如何」的陈述回到满足本身。给定一个把图中任一对送到 B 中取值的函数，只需施加那两个全称量词，并用取值读式的充分性等式把隶属事实换成前件的满足。至此，`valuesInAt` 的两个方向各有一条引理可用。
<!--ja-->
移転の定理には、値の制限の導入方向、つまり前に取り出されなかった方向、「グラフのすべての対についての主張」から充足そのものへ戻る方向が必要です。グラフの中の任意の対を B の値へ送る関数が与えられれば、二つの全称量化子を適用し、適用の読み式の妥当性の等式によって所属の事実を前件の充足へ変えます。これで `valuesInAt` の両方向が、方向ごとに一つの補題として使えるようになりました。
<!--/-->

```agda
valuesInAt-in : ∀ {n} (f B : Fin n) (γ : S ^ n)
              → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
                 → ⟨ fst y ∈ fst (lookup B γ) ⟩)
              → ⟨ γ ⊨ valuesInAt f B ⟩
valuesInAt-in f B γ k x y hp = k x y
```

<!--en-->
The theorem compares two assignments γ and γ', possibly of different arities, with three indices chosen on each side. The hypotheses are paths between the projected sets: the graph, the domain, and the value set are equal as sets of the hierarchy, element by element. Nothing is assumed about how the indices on the two sides relate, only about what the lookups return after projection; this is exactly the situation of a construction that re-indexes its environments.
<!--zh-->
定理比较两个环境 γ 与 `γ'`，二者元数可以不同，并在每侧各取三个指标。前提是投影后集合之间的路径：图、定义域与取值集合作为层级中的集合逐元素相等。对两侧指标之间的关系不作任何假设，只假设投影后查表所得一致；这正是一个用别的索引呈现其环境的构造所处的情形。
<!--ja-->
定理は、アリティの異なりうる二つの割り当て γ と `γ'` を比較し、各側で三つの添字を選びます。前提は射影された集合の間の経路、すなわちグラフ、定義域、値の集合が階層の集合として要素ごとに等しいことです。両側の添字同士の関係については何も仮定せず、射影後の検表の結果だけを仮定します。これはまさに、環境を別の添字づけで提示する構成の置かれた状況です。
<!--/-->

```agda
  (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ)) hp)

envOverAt-transport : ∀ {n n'} (γ : S ^ n) (γ' : S ^ n')
                      (e d B : Fin n) (e' d' B' : Fin n')
                    → fst (lookup e γ) ≡ fst (lookup e' γ')
                    → fst (lookup d γ) ≡ fst (lookup d' γ')
```

<!--en-->
Single-valuedness transfers by composing the extraction lemma at γ with the introduction lemma at γ'. Given two values y and y' recorded against x at γ', the hypothesis is first moved back to a satisfaction at γ along the path that identifies pair membership in the projected graph on the two sides; the extraction lemma then yields equality of the two projected values, and the introduction lemma repackages it as satisfaction at γ'. The equality itself needs no transport, since values are elements of S on both sides.
<!--zh-->
单值性的迁移是把 γ 处的消去引理与 `γ'` 处的引入引理复合。设在 `γ'` 处同一自变量 x 下记有两个取值 y 与 `y'`，先用「认同两侧投影图中对隶属」的路径把前提搬回 γ 一侧的满足；消去引理随后给出两个投影值相等，引入引理再把它包装成 `γ'` 处的满足。这个相等本身无需传输，因为两侧的取值都是 S 的元素。
<!--ja-->
一価性の移転は、γ での消去補題と `γ'` での導入補題の合成です。`γ'` で同じ入力 x に対する二つの値 y と `y'` が記録されていれば、まず両側の射影されたグラフにおける対の所属を同一視する経路に沿って、前提を γ 側の充足へ戻します。消去補題が二つの射影された値の相等を与え、導入補題がそれを `γ'` での充足として包み直します。相等そのものには輸送が要りません。両側の値とも S の要素だからです。
<!--/-->

```agda
                    → fst (lookup B γ) ≡ fst (lookup B' γ')
                    → ⟨ γ ⊨ envOverAt e d B ⟩ → ⟨ γ' ⊨ envOverAt e' d' B' ⟩
envOverAt-transport γ γ' e d B e' d' B' qe qd qb h =
    svAt-in e' γ' (λ x y y' p q →
      svAt-out e γ (envOver-sv e d B γ h) x y y'
```

<!--en-->
The domain clause transfers through the introduction lemma for `domAt`, supplying both implications at γ'. The first implication reads: having a value forces membership in the domain. From the merely truncated existence of a value, the extraction lemma at γ produces membership in the projected domain d, which needs no witness to be eliminated into, and the path qd carries that membership across to d'.
<!--zh-->
定义域一条经由 `domAt` 的引入引理迁移，在 `γ'` 处同时给出两个蕴含。第一个蕴含说：有取值就必在定义域中。从取值的仅仅被截断的存在出发，γ 处的消去引理给出对投影后定义域 d 的隶属，消去到隶属命题无需选定任何见证，再由路径 qd 把这条隶属搬到 `d'` 一侧。
<!--ja-->
定義域の条項は `domAt` の導入補題を通って移り、`γ'` で二つの含意をそろえて与えます。第一の含意は、値を持てば定義域に属する、というものです。値の切り詰められた存在だけから、γ での消去補題が射影された定義域 d への所属を生みます。所属という命題への消去には証人を選ぶ必要がなく、経路 qd がその所属を `d'` 側へ運びます。
<!--/-->

```agda
        (subst ⟨_⟩ (sym (at x y)) p) (subst ⟨_⟩ (sym (at x y')) q))
  , ( domAt-intro e' d' γ'
      (λ x → (λ m → subst (λ w → ⟨ fst x ∈ w ⟩) qd
                (PT.rec (snd (fst x ∈ fst (lookup d γ)))
                  (λ { (y , p) → domAt-out e d γ (envOver-dom e d B γ h) x y
```

<!--en-->
The second implication reads in the opposite direction: membership in the domain forces having a value. A membership in d' is first moved back along the symmetric path, the extraction lemma at γ then yields the merely truncated existence of an entry, and the truncation is transformed internally by replacing the body's satisfaction with its γ'-side form. The value y itself passes through untouched, which is correct: the two graphs agree only after projection, and the entries are elements of S.
<!--zh-->
第二个蕴含方向相反：在定义域中就必有取值。先把 `d'` 中的隶属沿对称路径搬回，γ 处的消去引理随即给出「有条目」的仅仅被截断的存在，再在截断内部把主体的满足换成 `γ'` 一侧的形式。取值 y 本身原样通过，这也正确：两个图只是投影后一致，而条目是 S 的元素。
<!--ja-->
第二の含意は逆向きで、定義域に属すれば値を持つ、というものです。まず `d'` での所属を対称な経路で戻し、γ での消去補題が「項目がある」ことの切り詰められた存在を与えます。そして切り詰めの内側で、本体の充足を `γ'` 側の形へ置き換えます。値の y 自身はそのまま通ります。これが正しいのは、二つのグラフが一致するのは射影後だけで、項目は S の要素だからです。
<!--/-->

```agda
                         (subst ⟨_⟩ (sym (at x y)) p) })
                  m))
            , (λ hx → PT.map (λ { (y , p) → y , subst ⟨_⟩ (at x y) p })
                (domAt-in e d γ (envOver-dom e d B γ h) x
                  (subst (λ w → ⟨ fst x ∈ w ⟩) (sym qd) hx))))
```

<!--en-->
For the value restriction, begin with a pair membership in the new projected graph. The symmetric graph-membership path moves it to the old graph; `valuesInAt-out` there yields membership of the value in the old set `B`; one forward transport along `qb : B ≡ B′` then gives membership in `B′`. Thus `qb` is used once, in the direction from the old value set to the new one.
<!--zh-->
迁移取值限制时，先从新投影图中的一条对隶属出发。沿图隶属路径的反向把它搬回旧图，随后旧环境处的 `valuesInAt-out` 给出该取值属于旧集合 `B`；最后沿 `qb : B ≡ B′` 正向搬运一次，得到它属于 `B′`。因此 `qb` 只使用一次，方向从旧取值集合到新取值集合。
<!--ja-->
値の制限では、新しい射影グラフへの対の所属から始めます。グラフ所属のパスを逆向きに使って旧グラフへ移し、そこで `valuesInAt-out` により値が旧集合 `B` に属することを得ます。最後に `qb : B ≡ B′` に沿って一度だけ順方向へ輸送し、`B′` への所属を得ます。したがって `qb` を使うのは旧値集合から新値集合への一回だけです。
<!--/-->

```agda
    , ( valuesInAt-in e' B' γ'
        (λ x y p → subst (λ w → ⟨ fst y ∈ w ⟩) qb
          (valuesInAt-out e B γ (envOver-values e d B γ h) x y
            (subst ⟨_⟩ (sym (at x y)) p)))
      , pairsIn-in e' d' B' γ'
```

<!--en-->
The pairs clause is the last to move, and the transports stay inside the truncation. Reading the clause out at γ gives, merely, witnesses u and v with their memberships in the projected d and B and the pair equation. The two memberships are carried to d' and B' by qd and qb respectively, while the equation `fst s ≡ pr (fst u) (fst v)` needs no transport at all: it speaks about underlying sets, and the hypotheses say exactly that those agree, so it is the same equation on both sides.
<!--zh-->
诸对一条最后迁移，而各次传输都留在截断之内。在 γ 处读出该条，仅仅是得到见证 u 与 v、二者对投影后 d 与 B 的隶属，以及对的等式。两条隶属分别由 qd 与 qb 搬到 `d'` 与 `B'`，而等式 `fst s ≡ pr (fst u) (fst v)` 完全无需传输：它谈的是底层集合，前提恰好说这些集合一致，故这条等式在两侧是同一条。
<!--ja-->
対の条項が最後に移り、輸送はすべて切り詰めの内側にとどまります。γ で条項を読み出すと、証拠 u と v、射影された d と B へのそれぞれの所属、そして対の等式が単に存在するとして得られます。二つの所属は qd と qb によってそれぞれ `d'` と `B'` へ運ばれます。一方、等式 `fst s ≡ pr (fst u) (fst v)` には輸送がまったく要りません。これは底にある集合についての主張であり、前提はまさにそれらが一致することを言っているので、等式は両側で同一です。
<!--/-->

```agda
        (λ s s∈ → PT.map
          (λ { (u , (v , (u∈ , (v∈ , eq)))) →
            u , (v , ( subst (λ w → ⟨ fst u ∈ w ⟩) qd u∈
                     , ( subst (λ w → ⟨ fst v ∈ w ⟩) qb v∈ , eq ) )) })
          (pairsIn-out e d B γ (envOver-pairs e d B γ h) s
```

<!--en-->
The remaining ingredient is the path `at`: for each x and y, the path identifying membership of the pair in the projected graph on the two sides. It is congruence, applying the equality qe of the two graphs to the membership predicate at fixed pair components. Every transport inside the theorem that concerns the graph goes through this one path, so the whole argument rests on the three given equalities and nothing hidden.
<!--zh-->
剩下的原料就是路径 `at`：对每个 x 与 y，认同两侧「该对属于投影后的图」的路径。它是同余性，即把两条图之间的等式 qe 作用到固定对分量的隶属谓词上。定理内部凡涉及图的传输都经过这一条路径，因此整个论证只依赖所给的三条等式，别无隐藏之物。
<!--ja-->
残りの材料は経路 `at` です。各 x と y に対し、両側で「その対が射影されたグラフに属する」ことを同一視する経路です。これは合同であり、二つのグラフの間の等式 qe を、対の成分を固定した所属述語に適用したものです。定理の内部でグラフに関わる輸送はすべてこの一つの経路を通るので、議論全体は与えられた三つの等式のみに依存し、隠れたものはありません。
<!--/-->

```agda
            (subst (λ w → ⟨ fst s ∈ w ⟩) (sym qe) s∈))) ) )
  where
  at : (x y : S) → (pr (fst x) (fst y) ∈ fst (lookup e γ))
                 ≡ (pr (fst x) (fst y) ∈ fst (lookup e' γ'))
  at x y = cong (λ w → pr (fst x) (fst y) ∈ w) qe
```

<!--en-->
## A container for pair components

Reading a pair-shaped code exposes its two components, and it is convenient to have both available as members of a single constructible set. The candidate is forced by the mathematics: if `fst x` is the ordered pair of `fst u` and `fst v`, then the unordered pair `⁅ fst u , fst v ⁆` is a member of `fst x`, hence itself constructible by transitivity of `L`, and both components are members of it. The section records exactly this witness together with the three membership facts, as a type `Container x u v` and a construction `container` producing it from the path `fst x ≡ pr (fst u) (fst v)`.
<!--zh-->
## 容纳配对分量

读取配对形状的码会暴露它的两个分量，而把二者同时呈现为**同一个**可构造集合的成员会带来方便。候选对象由数学本身决定：若 `fst x` 是 `fst u` 与 `fst v` 的有序对，则无序对 `⁅ fst u , fst v ⁆` 属于 `fst x`，故由 `L` 的传递性它自身可构造，且两个分量都是它的成员。本节记录的正是这个见证连同三条隶属事实：一个类型 `Container x u v`，以及从路径 `fst x ≡ pr (fst u) (fst v)` 造出它的构造 `container`。
<!--ja-->
## 対の成分を収める集合

対の形をした符号を読むと二つの成分が現れますが、両方を**ひとつの**構成可能集合の要素として持ち出せると便利です。候補は数学そのものが決めます。`fst x` が `fst u` と `fst v` の順序対なら、非順序対 `⁅ fst u , fst v ⁆` は `fst x` に属するので、`L` の推移性によりそれ自身構成可能であり、しかも二つの成分はどちらもその要素です。この節が記録するのは、まさにこの証拠と三つの所属の事実、すなわち型 `Container x u v` と、経路 `fst x ≡ pr (fst u) (fst v)` からそれを造る構成 `container` です。
<!--/-->

<!--en-->
The type packages one element `s` of the model with three ambient membership facts, all stated after projection: the underlying set of `s` is a member of `fst x`, and the underlying sets of `u` and `v` are members of `fst s`. No claim is made beyond these; in particular nothing asserts that `s` is the least such set. The construction `container` takes the hypothesis that `fst x` equals `pr (fst u) (fst v)` and returns the witness with its three certificates in one package.
<!--zh-->
该类型把模型的一个元素 `s` 与三条周遭隶属事实打包，全部在投影后陈述：`s` 的底集属于 `fst x`，而 `u`、`v` 的底集都属于 `fst s`。除此之外不作任何断言；特别地，它并不声称 `s` 是具有此性质的极小集合。构造 `container` 以「`fst x` 等于 `pr (fst u) (fst v)`」为前提，把见证连同三份证书一并返回。
<!--ja-->
この型は、モデルの要素 `s` に三つの周囲の所属の事実を、すべて射影後に述べる形でまとめます。`s` の底集合が `fst x` に属し、`u` と `v` の底集合がともに `fst s` に属するというものです。それ以外の主張はなく、とりわけ `s` がこの性質を持つ極小の集合であるとは言いません。構成 `container` は「`fst x` が `pr (fst u) (fst v)` に等しい」という仮定を受け取り、証拠と三つの証明書をひとまとめにして返します。
<!--/-->

```agda
Container : (x u v : S) → Type (ℓ-suc ℓ)
Container x u v = Σ[ s ∈ S ] (⟨ fst s ∈ fst x ⟩ × (⟨ fst u ∈ fst s ⟩ × ⟨ fst v ∈ fst s ⟩))

opaque
  container : (x u v : S) → fst x ≡ pr (fst u) (fst v) → Container x u v
  container x u v e = s , (s∈ , (∈pair-introL refl , ∈pair-introR refl))
```

<!--en-->
The witness is the unordered pair of the two underlying sets. As one member of the outer unordered pair in the Kuratowski encoding, it belongs to `pr (fst u) (fst v)` by the introduction rule at the reflexive path, and transporting along the hypothesis `e` moves that membership into membership in `fst x`. This is precisely the input transitivity of `L` consumes: since the unordered pair is a member of a constructible set, `isL-trans` yields it as an element of `S`, certificate included. The two remaining memberships, of `fst u` and `fst v` in it, are the two introduction rules at reflexive paths.
<!--zh-->
见证就是两个底集的无序对。作为 Kuratowski 编码之外层无序对的一个成员，它在自反路径上的引入规则下属于 `pr (fst u) (fst v)`，沿前提 `e` 传输后便成为对 `fst x` 的隶属。而这恰是 `L` 传递性所消费的输入：既然该无序对属于一个可构造集合，`isL-trans` 便把它连同证书一起作为 `S` 的元素给出。余下的两条隶属，即 `fst u` 与 `fst v` 属于它，则由自反路径上的两条引入规则给出。
<!--ja-->
証拠は、二つの底集合の非順序対です。Kuratowski 符号の外側の非順序対の一要素として、反射経路での導入規則により `pr (fst u) (fst v)` に属し、仮定 `e` に沿って輸送すれば `fst x` への所属になります。これこそ `L` の推移性が受け取る入力です。非順序対が構成可能な集合に属する以上、`isL-trans` はそれを証明書込みで `S` の要素として与えます。残る二つの所属、すなわち `fst u` と `fst v` がそれに属することは、反射経路での二つの導入規則によります。
<!--/-->

```agda
    where
    s∈ : ⟨ ⁅ fst u , fst v ⁆ ∈ fst x ⟩
    s∈ = subst (λ w → ⟨ ⁅ fst u , fst v ⁆ ∈ w ⟩) (sym e) (∈pair-introR refl)
    s : S
    s = ⁅ fst u , fst v ⁆ , isL-trans s∈ (snd x)

```

<!--en-->
## Recap

The chapter closes the gap between the two sides of the semantics. Formulas are satisfied in `L`, at environments of constructible elements, while the concrete facts they need to express are ambient facts about underlying sets; the dictionary entries connect the two by exact adequacy paths. Ordered pair recognition is absolute, graph membership acquires a constructible witness through transitivity, and the environment description collects single-valuedness, exact domain, value restriction, and the pairs clause, depending only on the three projected sets. Syntax coding then instantiates inside `L` itself, and the bridge shows that internal codes project to the ambient codes of the projected formulas, so the hierarchy-side readers apply to internally built codes. The container supplies, for a pair-shaped code, one constructible set holding both components.
<!--zh-->
## 小结

本章弥合了语义两侧之间的裂缝。公式在 `L` 中、在由可构造元素组成的环境处被满足，而它们需要表达的具体事实却是关于底集的周遭事实；词典各词条以精确的充分性路径把两侧连起来。有序对识别是绝对的；图的隶属经传递性获得可构造的见证；环境描述汇集了单值性、恰当定义域、取值限制与诸对条目，且只依赖三个投影后的集合。语法符号化随之在 `L` 内部实例化，桥定理表明内部码投影为投影后公式的周遭码，于是写在层级一侧的读式可以施于内部造出的码。容器则为配对形状的码给出一个同时容纳两个分量的可构造集合。
<!--ja-->
## まとめ

本章は、意味論の両側の間を埋めました。論理式は `L` の中で、構成可能な要素からなる環境のもとで充足されますが、表現すべき具体的な事実は底集合についての周囲の事実です。辞書の各項目は、正確な妥当性の経路によってこの二つを結びます。順序対の認識は絶対的であり、グラフの所属は推移性によって構成可能な証拠を獲得し、環境の記述は一価性、ちょうどの定義域、値の制限、対の条項を集めて、射影された三つの集合だけに依存します。構文の符号化は続いて `L` 自身の中で実例化され、橋渡しの定理は、内部の符号が射影された論理式の周囲の符号へ射影されることを示すので、階層の側で書かれた読み式が内部で造られた符号に適用できます。容器は、対の形をした符号に対して、二つの成分をともに収める構成可能な集合をひとつ供給します。
<!--/-->
