<!--en-->
# Constant bounding

A formula is bounded by a predicate when every constant occurrence satisfies that predicate. These structural certificates support weakening along predicate implication and allow a partially defined constant map to relabel exactly the formulas on which it is defined.

This chapter is that certificate. `BoundedFo P φ` records, occurrence by occurrence, that every constant appearing in `φ` satisfies `P`. It is defined by the same case analysis as the formula it inspects, so it splits automatically under pattern matching, and no proof ever has to reason about a list of the constants of a formula. Being pure syntax, the chapter mentions neither hierarchies nor stages, and introduces no extra cost.

The companion is monotonicity. A certificate for a narrower predicate is one for a wider predicate, which is how certificates written against different stages are brought to a common stage before being used together.
<!--zh-->
# 常元有界性

当公式中每次出现的常元都满足一个谓词时，称该公式受此谓词约束。这些结构化证书可随谓词的蕴含而放宽，并使部分定义的常元映射恰好能对其定义域内的公式作常元改名。

本章就是那份证书。`BoundedFo P φ` 逐次出现地记录：`φ` 中出现的每个常元都满足 `P`。它按被检查公式所用的同一套分情形定义，故在模式匹配下自动拆开，任何证明都不必对「公式的常元列表」作推理。由于是纯语法，本章既不提层级也不提阶段，也不引入额外代价。

配套的是单调性。窄谓词的证书同时就是宽谓词的证书；这正是把针对不同阶段写下的证书转到公共阶段、以便一并使用的办法。
<!--ja-->
# 定数の有界性

論理式に現れる定数がすべて与えられた述語を満たすとき、その論理式はその述語で有界です。この構造的な証明書は述語の含意に沿って弱められ、部分的に定義された定数写像を、その定義域に収まる論理式へ適用できるようにします。

本章はその証明書そのものです。`BoundedFo P φ` は、`φ` に現れるすべての定数の出現ごとに `P` を満たすことを記録します。証明書は検査対象の論理式と同じ場合分けで定義されるため、パターン照合の下で自動的に分解され、いかなる証明も「論理式の定数のリスト」について推論する必要はありません。純粋な構文だけを扱うので、本章は階層も段階も言及せず、追加のコストも生じません。

これに伴うのが単調性です。より狭い述語に対する証明書は、より広い述語に対する証明書でもあります。異なる段階に対して書かれた証明書を、共通の段階へ移してから併せて使うのが、まさにこの仕組みです。
<!--/-->

<!--en-->
Why should a formula come with a certificate about its constants? Consider a map on constants that is only partially defined: it sends a constant `c` to a new constant exactly when `c` satisfies some predicate `P`. Such a map cannot act on an arbitrary formula, because the formula might mention a constant outside its domain. But if we are handed, for each constant occurrence in the formula, a proof that this occurrence lies in the domain, then the map can act everywhere the formula needs it to. The question this chapter answers is: what is the right shape for that per-occurrence evidence, and what does it buy us?
<!--zh-->
为什么公式要附带一份关于其常元的证书？设想一个只被部分定义的常元映射：当常元 `c` 满足某个谓词 `P` 时，它把 `c` 送到新的常元。这样的映射无法作用于任意公式，因为公式可能提到定义域之外的常元。但若我们对公式中的每次常元出现都拿到一份「该出现落在定义域内」的证明，映射就能在公式需要之处处处作用。本章要回答的问题是：这种逐出现证据应取什么形状，它又能带来什么？
<!--ja-->
なぜ論理式は定数についての証明書を伴うべきなのでしょうか。部分的にしか定義されていない定数上の写像を考えてみてください。定数 `c` が述語 `P` を満たすときに限り、その写像は `c` を新しい定数へ送ります。このような写像は任意の論理式に適用できるとは限りません。式が定義域の外の定数を含むかもしれないからです。しかし、式の中の各定数の出現について「この出現は定義域に収まる」という証明が揃っていれば、写像は式が必要とするすべての場所で作用できます。本章が答える問いは、この出現ごとの証拠はどのような形をすべきか、そしてそれから何が得られるか、ということです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module FOL.Manipulation.ConstantBounding where

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
```

<!--en-->
The answer is a definition that follows the shape of the syntax itself. A term is either a constant, which must come with a proof of `P`, or a variable, which mentions no constant and so imposes no condition; a formula is built from these, and its certificate is assembled from the certificates of its parts. Because the certificate mirrors the constructor structure of `Term K n` and `Formula K n`, matching against it delivers exactly the domain proof at each constant occurrence. Two later uses shape the design: the monotonicity section transports certificates along an implication of predicates, and the relabelling section feeds them to the partial map; the Δ₀ constructors are imported so the relabelled formula can keep its Lévy-hierarchy witness, and the unit type supplies the trivial certificate carried by anything with no constants.
<!--zh-->
答案是一个随语法形状而定的定义。词项要么是常元，必须附带 `P` 的证明；要么是变量，不含常元，因此不施加任何条件。公式由这些构造而成，其证书也由各部分的证书组装而成。由于证书镜像了 `Term K n` 与 `Formula K n` 的构造子结构，对其作匹配就会在每次常元出现处恰好交付定义域证明。两处后续用途塑造了设计：单调性一节沿谓词间的蕴含传递证书，改名一节把证书交给部分映射；引入 Δ₀ 构造子是为了让改名后的公式保住其 Lévy 层级见证，而 Unit 类型则为一切不含常元者提供平凡证书。
<!--ja-->
その答えが、構文の形そのものに沿った定義です。項は定数であるなら `P` の証明を伴わねばならず、変数なら定数を含まないので条件を課しません。論理式はこれらから組み立てられ、その証明書も各部分の証明書から組み上がります。証明書は `Term K n` と `Formula K n` の構成子構造を写しているので、それに対する照合は各定数の出現箇所で定義域の証明をちょうど届けてくれます。設計を形づくるのは二つの後の用途です。単調性の節は述語の含意に沿って証明書を移し、改名の節は証明書を部分写像に渡します。Δ₀ の構成子は、改名後の論理式が Lévy 階層の証拠を保てるように読み込まれ、Unit 型は定数を含まないものが持つ自明な証明書を供給します。
<!--/-->

```agda
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )

open import Cubical.Data.Unit using ( Unit )
```

<!--en-->
## The certificate

`BoundedTm P`{.Agda} and `BoundedFo P`{.Agda} mirror the syntax: constants carry proofs of `P`, variables carry trivial data, and compound formulas pair the certificates of their parts. Pattern matching therefore exposes precisely the evidence needed at each constant occurrence.
<!--zh-->
## 证书

`BoundedTm P`{.Agda} 与 `BoundedFo P`{.Agda} 随语法结构而定：常元携带 `P` 的证明，变量携带平凡数据，复合公式则配有其各部分的证书。因此，模式匹配会在每次常元出现处恰好给出所需证据。
<!--ja-->
## 証明書

`BoundedTm P`{.Agda} と `BoundedFo P`{.Agda} は構文をそのまま映します。定数は `P` の証明を持ち、変数は自明なデータを持ち、複合論理式は各部分の証明書を組にします。そのため、パターン照合によって各定数の出現箇所で必要な証拠だけが得られます。
<!--/-->

<!--en-->
Start with terms, where the condition is simplest. Take a predicate `P` on constants and a term such as `c ∈̇ var i` built from a constant `c` and a variable. The certificate `BoundedTm P t` is defined by recursion on `t`: for `con c` it is `P c` itself, the domain proof at that occurrence, while for `var i` it is `Lift Unit`, the unit type raised to the level of `P c` so that both cases have type `Type ℓp`. A variable asks for nothing; its trivial certificate simply fills the slot.
<!--zh-->
从条件最简单的词项入手。取常元上的谓词 `P` 和一个由常元 `c` 与变量构成的词项，如 `c ∈̇ var i`。证书 `BoundedTm P t` 对 `t` 递归定义：对 `con c`，证书就是 `P c` 本身，即该出现处的定义域证明；对 `var i`，证书是 `Lift Unit`，即提升到 `P c` 所在层级的单元素类型，使两种情形类型均为 `Type ℓp`。变量一无所求；其平凡证书只是把空位填上。
<!--ja-->
条件が最も単純な項から始めましょう。定数上の述語 `P` と、定数 `c` と変数からなる `c ∈̇ var i` のような項を取ります。証明書 `BoundedTm P t` は `t` に対する再帰で定義されます。`con c` に対しては証明書は `P c` そのものであり、これがその出現での定義域の証明です。`var i` に対しては `Lift Unit`、すなわち `P c` と同じレベルへ持ち上げた単元型であり、両方の場合が型 `Type ℓp` を持つようにします。変数は何も要求しないので、その自明な証明書が空所を埋めるだけです。
<!--/-->

```agda
BoundedTm : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Term K n → Type ℓp
BoundedTm P (con c) = P c
BoundedTm P (var i) = Lift Unit

BoundedFo : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Formula K n → Type ℓp
BoundedFo P (t ∈̇ u)  = BoundedTm P t × BoundedTm P u
```

<!--en-->
The recursion pattern is uniform: whenever a constructor has term or formula arguments, its certificate is the product of theirs; whenever a constructor mentions no constant, its certificate is trivial. For example, in `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)` with two occurrences of the constant `c`, the certificate is a fourfold pairing that ends in two copies of the proof `P c`: one per occurrence, in the position where the occurrence sits. In contrast, `⊥̇` and bare variables carry nothing but `Lift Unit`. So the certificate follows occurrences, not the constant symbols abstractly: the same constant occurring twice contributes two proofs.
<!--zh-->
递归模式是统一的：凡构造子带有词项或公式参数，其证书就是各参数证书的乘积；凡构造子不提及常元，其证书就是平凡的。例如在 `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)` 中常元 `c` 出现两次，证书是一个四重配对，末端是两份 `P c` 的证明：每次出现一份，位置与出现的位置对应。相反，`⊥̇` 与裸变量只携带 `Lift Unit`。所以证书跟随的是出现，而不是抽象的常元符号：同一常元出现两次就贡献两份证明。
<!--ja-->
再帰のパターンは一様です。構成子が項や論理式の引数を持つなら、その証明書は引数の証明書の積になり、構成子が定数に触れないなら、その証明書は自明です。たとえば `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)` では定数 `c` が二回現れますが、証明書は四重の組であり、その末端に証明 `P c` が二部、それぞれの出現の位置に対応して入ります。逆に `⊥̇` や素の変数が持つのは `Lift Unit` だけです。つまり証明書は抽象的な定数記号ではなく出現に従い、同じ定数が二回現れれば証明も二部になります。
<!--/-->

```agda
BoundedFo P (t ≐ u)  = BoundedTm P t × BoundedTm P u
BoundedFo P (φ ∧̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ∨̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ⇒̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P ⊥̇        = Lift Unit
```

<!--en-->
Quantifiers bind variables and therefore leave constants untouched, so the unbounded forms pass their body's certificate through unchanged. A bounded quantifier, however, carries a bounding term that may mention constants: for `∀̇∈ t φ` the certificate pairs the term certificate for `t` with the formula certificate for `φ`, exactly as our example formula `∃̇ (var 0 ≐ c)` shows, where the outer body's certificate is just the certificate of `var 0 ≐ c`. These clauses exhaust the constructors of `Formula K n`, and each clause is read off the shape of the formula rather than computed by searching it.
<!--zh-->
量词约束的是变量，因此不触及常元，无界形式就把主体的证书原样传出。但带界量词携带一个可能提及常元的界定词项：对 `∀̇∈ t φ`，证书把 `t` 的词项证书与 `φ` 的公式证书配对，正如例式 `∃̇ (var 0 ≐ c)` 所示，其主体的证书就是 `var 0 ≐ c` 的证书。这些子句穷尽了 `Formula K n` 的构造子，而且每条子句都是从公式形状直接读出的，不是靠搜索计算出来的。
<!--ja-->
量化子は変数を束縛するので定数には触れず、非有界の形式は本体の証明書をそのまま通します。しかし有界量化子は定数を含みうる界の項を伴うので、`∀̇∈ t φ` の証明書は `t` の項の証明書と `φ` の論理式の証明書の組になります。例の式 `∃̇ (var 0 ≐ c)` が示すとおり、その本体の証明書は `var 0 ≐ c` の証明書にほかなりません。これらの節は `Formula K n` の全構成子を尽くし、各節は式の形から直接読み取られるのであって、探索によって計算されるのではありません。
<!--/-->

```agda
BoundedFo P (∃̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇∈ t φ) = BoundedTm P t × BoundedFo P φ
BoundedFo P (∃̇∈ t φ) = BoundedTm P t × BoundedFo P φ
```

<!--en-->
## Monotonicity

If `P` implies `Q`, every `P`-bounded term or formula is also `Q`-bounded. The proof follows the certificate structure and later lets bounds established at smaller stages be reused at larger stages.
<!--zh-->
## 单调性

若 `P` 蕴含 `Q`，则每个受 `P` 约束的词项或公式也受 `Q` 约束。证明沿证书结构进行，随后可将在较小阶段建立的界复用于较大阶段。
<!--ja-->
## 単調性

`P` が `Q` を含意するなら、`P` で有界な項や論理式は `Q` でも有界です。証明は証明書の構造に従い、後には小さい段階で得た有界性を大きい段階で再利用できます。
<!--/-->

<!--en-->
Certificates are only useful if they can be moved between predicates. Think of a predicate as restricting which constants are allowed: widening `P` to `Q` along a pointwise implication `P⊆Q` cannot invalidate any certificate, since every occurrence accepted by `P` is still accepted by `Q`. For a single constant this is one application: `P⊆Q c` turns the proof `P c` into `Q c`. `BoundedTm-mono` extends this to whole terms by recursion: the constant case performs that single application, and the variable case passes through, since `Lift Unit` is inhabited regardless of the predicate.
<!--zh-->
证书只有在能于谓词之间移动时才有用。把谓词想成对允许常元的限制：沿逐点蕴含 `P⊆Q` 把 `P` 放宽为 `Q` 不会使任何证书失效，因为被 `P` 接受的每次出现仍被 `Q` 接受。对单个常元这是一次应用：`P⊆Q c` 把证明 `P c` 变成 `Q c`。`BoundedTm-mono` 对整个词项递归地扩展这一点：常元情形做那一次应用，变量情形直接通过，因为 `Lift Unit` 无论谓词如何都有元素。
<!--ja-->
証明書は、述語の間で移せてこそ有用です。述語を許される定数の制限と考えれば、各点的含意 `P⊆Q` に沿って `P` を `Q` へ広げても証明書は無効になりません。`P` が受け入れる出現は `Q` も受け入れるからです。単一の定数に対してはこれは一度の適用にすぎず、`P⊆Q c` が証明 `P c` を `Q c` へ変えます。`BoundedTm-mono` はこれを項全体へ再帰で拡張します。定数の場合はその一度の適用を行い、変数の場合は素通りします。`Lift Unit` は述語にかかわらず要素を持つからです。
<!--/-->

```agda
module _ {ℓk ℓp ℓq} {K : Type ℓk} {P : K → Type ℓp} {Q : K → Type ℓq}
         (P⊆Q : (c : K) → P c → Q c) where

  BoundedTm-mono : ∀ {n} (t : Term K n) → BoundedTm P t → BoundedTm Q t
  BoundedTm-mono (con c) p = P⊆Q c p
  BoundedTm-mono (var i) _ = _
```

<!--en-->
The same argument lifts to formulas through their certificates' products. For our example `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)`, a `P`-certificate is four proofs against `P`; applying `BoundedTm-mono` to each term slot and the recursion to each subformula turns them into four proofs against `Q`, and the formula's shape never changes.
<!--zh-->
同一论证经证书的乘积提升到公式。以例式 `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)` 为例，一份 `P` 证书是四份关于 `P` 的证明；对每个词项空位施加 `BoundedTm-mono`、对每个子公式施加递归，就把它们变成四份关于 `Q` 的证明，而公式的形状自始至终不变。
<!--ja-->
同じ議論は、証明書の積を通じて論理式へ持ち上がります。例の `(c ∈̇ d) ∧̇ ∃̇ (var 0 ≐ c)` では、`P` の証明書は `P` についての四つの証明です。各項の空所に `BoundedTm-mono` を、各部分式に再帰を適用すれば、それらは `Q` についての四つの証明になり、式の形は终始変わりません。
<!--/-->

```agda

  BoundedFo-mono : ∀ {n} (φ : Formula K n) → BoundedFo P φ → BoundedFo Q φ
  BoundedFo-mono (t ∈̇ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (t ≐ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (φ ∧̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono (φ ∨̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
```

<!--en-->
Nothing about this conversion is special to any connective: the atomic and propositional cases each split the certificate into its two factors, convert the factors, and re-pair them, while `⊥̇` needs only the trivial inhabitant. Conjunction, disjunction and implication are three spellings of one step.
<!--zh-->
这一转换对任何联结词都没有特殊性：原子式与命题联结词的情形都是把证书拆成两个因子、转换因子、再重新配对，而 `⊥̇` 只需平凡证据。合取、析取、蕴涵是同一步骤的三种写法。
<!--ja-->
この変換はどの接続詞にとっても特別ではありません。原子式と命題接続詞の場合はいずれも証明書を二つの因子に分け、因子を変換してから組み直すだけで、`⊥̇` は自明な証拠を渡すだけです。連言、選言、含意は同じ一歩を三通りに綴ったものです。
<!--/-->

```agda
  BoundedFo-mono (φ ⇒̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono ⊥̇        _         = _
  BoundedFo-mono (∃̇ φ)    hφ        = BoundedFo-mono φ hφ
```

<!--en-->
The quantifier cases finish the induction. Under `∃̇` or `∀̇` the body is converted recursively; under a bounded quantifier the bounding term's certificate is converted too, since the term may hold constants of its own. The result: widening the predicate widens every certificate, which is what lets bounds proved at one stage be quoted at another.
<!--zh-->
量词情形完成归纳。在 `∃̇` 或 `∀̇` 之下，主体被递归转换；在带界量词之下，界定词项的证书也被转换，因为该词项可能自带常元。结论是：放宽谓词就放宽了所有证书，这正是使在一个阶段证明的界能在另一阶段引用的原因。
<!--ja-->
量化子の場合で帰納が終わります。`∃̇` や `∀̇` の下では本体が再帰的に変換され、有界量化子の下では界の項が自らの定数を持ちうるため、その証明書も変換されます。結論として、述語を広げればすべての証明書が広がり、ある段階で示した有界性を別の段階で引用できるのはこのためです。
<!--/-->

```agda
  BoundedFo-mono (∀̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
  BoundedFo-mono (∃̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
```

<!--en-->
## Relabelling, partially

A partial map can relabel a bounded formula because its certificate supplies the domain proof at every constant occurrence. The resulting formula agrees after both source and target are mapped into a common type, and its Lévy witness is preserved.

The interface is stated in the generality its user needs. Two domains, a common world they both map into, a predicate on the source, a partial map defined under it, and the equation saying the partial map agrees with the two projections. In the intended instance the source is the model's carrier, the target is a stage's member type, the world is the hierarchy, and the equation is the fact that a member of a stage, viewed as a set, is the set it was.
<!--zh-->
## 部分常元改名

部分映射能为有界公式作常元改名，因为证书在每次常元出现处提供定义域证明。将源与目标都映入同一类型后，所得公式与原式相符，并且其 Lévy 见证得以保持。

接口按使用者所需的一般性陈述：给定两个域、它们共同映入的一个世界、源上的一个谓词，以及在该谓词之下有定义的一个部分映射，另有一条等式说明该部分映射与两个投影相符。在预期的实例中，源是模型的载体，目标是某个阶段的成员类型，世界是层级，而那条等式表达的是「阶段的成员作为集合来看，仍是它原本那个集合」这一事实。
<!--ja-->
## 部分的な定数の改名

部分写像は、有界性の証明書から各定数の出現箇所で定義域の証明を受け取り、有界な論理式の定数を改名できます。始域と終域を共通の型へ写せば結果は元の論理式と一致し、Lévy の証人も保存されます。

このインターフェイスは、利用者が必要とする一般性で述べられています。二つの定義域、両者がともに写し込まれる共通の世界、始域上の述語、その述語の下で定義された部分写像、そして部分写像が二つの射影と一致することを言う等式です。意図された具体例では、始域はモデルの台、終域はある段階のメンバー型、世界は階層であり、等式は「段階のメンバーを集合として見れば、それは元の集合そのものである」という事実です。
<!--/-->

<!--en-->
Now the certificate meets its consumer. A partial constant map is given by a domain predicate `P` on a source set `K` of constants and an assignment `down` defined only on `P`. To relabel a whole formula we also need a target set `K'` of constants and a world `W` into which both `K` and `K'` map. The mathematical condition on this data is a commuting triangle: each source constant `c` with `p : P c` lands, via `down` and then the target's map, on the same world element as `c` itself reaches by the source's map. When such a triangle is supplied, the relabelling it induces can be checked to agree with the original after both are read in `W`.
<!--zh-->
现在证书遇到了它的使用者。部分常元映射由源常元集 `K` 上的定义域谓词 `P` 与只在 `P` 上有定义的赋值 `down` 给出。要对整条公式改名，还需要目标常元集 `K'`，以及一个 `K` 与 `K'` 都映入的世界 `W`。对这些数据的数学条件是一个交换三角：对满足 `p : P c` 的每个源常元 `c`，先经 `down` 再经目标映射所落之处，与 `c` 经源映射所到之处是同一个世界元素。供给了这样的三角，由此诱导的改名在与原式都读入 `W` 之后便可验证相符。
<!--ja-->
いま証明書がその利用者に出会います。部分的な定数写像は、源の定数集合 `K` 上の定義域述語 `P` と、`P` の上でのみ定義された割り当て `down` で与えられます。論理式全体を改名するには、さらに先の定数集合 `K'` と、`K` と `K'` の双方が写し込まれる世界 `W` が必要です。このデータへの数学的な条件は可換な三角形です。`p : P c` を満たす各源の定数 `c` は、`down` を経て先の写像に渡った先が、`c` が源の写像で到達する世界の要素と一致しなければなりません。この三角形が与えられれば、そこから誘導される改名は、元の式とともに `W` で読んだとき一致すると検証できます。
<!--/-->

```agda
module Relabel
  {ℓk ℓk' ℓv ℓp : Level}
  {K  : Type ℓk}
  {K' : Type ℓk'}
  {W  : Type ℓv}
```

<!--en-->
The triangle appears here as the parameter `down-correct`: for every `c` and `p : P c`, the path `up (down c p) ≡ proj c`. This is the only correctness obligation on the data; everything else about the relabelling will follow from it occurrence by occurrence. Note that `down` needs the proof `p` as an argument: the certificate is what makes the partial map applicable, supplying its domain condition exactly where the formula mentions a constant.
<!--zh-->
这个三角在此以参数 `down-correct` 出现：对每个 `c` 与 `p : P c`，有一条路径 `up (down c p) ≡ proj c`。这是对数据的唯一正确性义务；改名的一切其余性质都将逐出现地从它推出。注意 `down` 需要证明 `p` 作为参数：证书正是使部分映射可施用的东西，恰在公式提及常元之处供给其定义域条件。
<!--ja-->
この三角形はここではパラメータ `down-correct` として現れます。すべての `c` と `p : P c` に対するパス `up (down c p) ≡ proj c` です。これがデータへの唯一の正しさの義務であり、改名に関するそれ以外のことはすべて、出現ごとにここから従います。`down` が証明 `p` を引数として要求する点に注意してください。部分写像を適用可能にするのは証明書であり、式が定数に触れるその箇所で定義域の条件を供給するのです。
<!--/-->

```agda
  (proj : K → W)
  (up   : K' → W)
  (P    : K → Type ℓp)
  (down : (c : K) → P c → K')
  (down-correct : (c : K) (p : P c) → up (down c p) ≡ proj c)
```

<!--en-->
Relabelling a term now just threads the certificate through. `liftTm` takes `t` together with `h : BoundedTm P t`; matching `h` at the constant node hands over precisely the proof `p : P c` that `down c` requires, so the node becomes `con (down c p)`. At a variable, `h` is trivial and the node passes through. The partial map has become total, but only on terms that present their domain proofs.
<!--zh-->
对词项改名只需把证书穿起来。`liftTm` 接受 `t` 连同 `h : BoundedTm P t`；在常元结点对 `h` 作匹配，恰好交出 `down c` 所需的证明 `p : P c`，于是结点变成 `con (down c p)`。在变量处，`h` 是平凡的，结点原样通过。部分映射变成了全映射，但只对出示定义域证明的词项如此。
<!--ja-->
項の改名は、証明書を通して配線するだけです。`liftTm` は `t` と `h : BoundedTm P t` を受け取り、定数の節点で `h` を照合すれば、`down c` が必要とする証明 `p : P c` がちょうど渡され、節点は `con (down c p)` になります。変数では `h` は自明で、節点はそのまま通ります。部分写像は全域的になりますが、それは定義域の証明を提示する項の上でのみです。
<!--/-->

```agda
  where

  liftTm : ∀ {n} (t : Term K n) → BoundedTm P t → Term K' n
  liftTm (con c) p = con (down c p)
  liftTm (var i) _ = var i

  liftFo : ∀ {n} (φ : Formula K n) → BoundedFo P φ → Formula K' n
```

<!--en-->
For a formula, `liftFo` applies `liftTm` at the term slots and recurses elsewhere. In our running example, the two occurrences of `c` are replaced by `down c` at its two proofs, `d` likewise, and the bound variable structure is untouched: relabelling only rewrites constants, never de Bruijn indices, so the free-variable count stays `n`.
<!--zh-->
对公式，`liftFo` 在词项空位施加 `liftTm`，其余处递归。在前面的例子中，`c` 的两次出现被替换为 `down c` 在其两份证明处的值，`d` 同理，而约束变元结构不受影响：改名只改写常元，从不触及 de Bruijn 指标，因此自由变元个数仍为 `n`。
<!--ja-->
論理式に対しては、`liftFo` が項の空所に `liftTm` を適用し、その他の場所では再帰します。先の例では、`c` の二つの出現がその二つの証明における `down c` の値に置き換えられ、`d` も同様で、束縛変数の構造はそのままです。改名が書き換えるのは定数だけで、de Bruijn 指標には触れないので、自由変数の個数は `n` のままです。
<!--/-->

```agda
  liftFo (t ∈̇ u)  (ht , hu) = liftTm t ht ∈̇ liftTm u hu
  liftFo (t ≐ u)  (ht , hu) = liftTm t ht ≐ liftTm u hu
  liftFo (φ ∧̇ ψ)  (hφ , hψ) = liftFo φ hφ ∧̇ liftFo ψ hψ
  liftFo (φ ∨̇ ψ)  (hφ , hψ) = liftFo φ hφ ∨̇ liftFo ψ hψ
  liftFo (φ ⇒̇ ψ)  (hφ , hψ) = liftFo φ hφ ⇒̇ liftFo ψ hψ
```

<!--en-->
The bounded quantifiers repeat the same two-part shape, relabelling their bounding term and recursing into their body, while `⊥̇` and the unbounded quantifiers contribute no constants to relabel. So `liftFo φ h` is always defined for a certified formula, and the agreement theorem of the next section says precisely in what sense it is the same formula as `φ`.
<!--zh-->
带界量词重复同样的两件套形状：对界定词项改名并对主体递归；`⊥̇` 与无界量词则没有可改名的常元。于是对任何携带证书的公式，`liftFo φ h` 总有定义，下一节的相符定理将精确说明它在何种意义上与 `φ` 是同一条公式。
<!--ja-->
有界量化子は同じ二部構成を繰り返し、界の項の定数を改名して本体に再帰します。`⊥̇` と非有界量化子は改名すべき定数を持ちません。したがって証明書を持つ論理式に対しては `liftFo φ h` はつねに定義され、次の節の一致定理が、それがどの意味で `φ` と同じ論理式なのかを正確に述べます。
<!--/-->

```agda
  liftFo ⊥̇        _         = ⊥̇
  liftFo (∃̇ φ)    hφ        = ∃̇ liftFo φ hφ
  liftFo (∀̇ φ)    hφ        = ∀̇ liftFo φ hφ
  liftFo (∀̇∈ t φ) (ht , hφ) = ∀̇∈ (liftTm t ht) (liftFo φ hφ)
  liftFo (∃̇∈ t φ) (ht , hφ) = ∃̇∈ (liftTm t ht) (liftFo φ hφ)
```

<!--en-->
Correctness says the relabelling changed nothing that matters: pushing the result into the common world `W` along `up` gives the same formula as pushing the original along `proj`. That is the equation at which the two branches of an absoluteness argument meet, and it holds occurrence by occurrence for exactly the reason the interface `down-correct` demanded. The Δ₀ witness survives as well: the certificate records quantifier structure only, so it transfers unchanged under a relabelling of constants.
<!--zh-->
正确性说明这次常元改名没有改变任何要紧的东西：沿 `up` 把结果推进共同世界 `W`，与沿 `proj` 把原式推进去，得到的是同一条公式。那正是绝对性论证中两条途径会合时所需的等式，而它逐次出现地成立，理由正是接口 `down-correct` 所索取的那一条。Δ₀ 见证同样得以保留：该证书记录的只是量词结构，在常元改名之下原样转移。
<!--ja-->
正しさとは、定数の改名が本質的な何も変えていないことを言います。`up` に沿って結果を共通の世界 `W` へ押し込んだものが、`proj` に沿って元の論理式を押し込んだものと同じ論理式になる、ということです。これは絶対性の議論で二つの経路が合流する等式であり、各出現ごとに、インターフェース `down-correct` が要求した理由によってまさに成立します。Δ₀ の証拠もまた保存されます。この証拠が記録するのは量化子構造だけなので、定数の改名の下でそのまま移ります。
<!--/-->

<!--en-->
Two facts close the story of the triangle. First, relabelling the lifted term into the common constant domain `W` along `up` yields the same term as relabelling the original along `proj`; second, relabelling preserves the Δ₀ certificate, since it changes constants but no quantifier structure. The base case is a term. For the constant `con c`, the certificate provides `p : P c`, and the desired path is just the triangle's edge `down-correct c p` placed under `cong con`. For `var i` both sides compute to `mapTm _ (var i)` applied to the same variable, so the path is `refl`.
<!--zh-->
两件事实为三角的故事收尾。其一，把提升后的词项沿 `up` 改名到共同常元域 `W`，与把原词项沿 `proj` 改名所得的词项相同；其二，改名保持 Δ₀ 证书，因为它改动的是常元而非量词结构。基例是词项。对常元 `con c`，证书提供 `p : P c`，所需路径就是把三角的边 `down-correct c p` 经 `cong con` 放置。对 `var i`，两边都计算为对同一变量的 `mapTm _ (var i)`，故路径是 `refl`。
<!--ja-->
三角形の物語を閉じるのは二つの事実です。第一に、持ち上げた項を `up` に沿って共通の定数域 `W` へ改名したものは、元の項を `proj` に沿って改名した項と一致します。第二に、改名は Δ₀ の証明書を保存します。変わるのは定数であって量化子構造ではないからです。基底は項です。定数 `con c` では証明書が `p : P c` を供給し、求めるパスは三角形の辺 `down-correct c p` を `cong con` の下に置いたものです。`var i` では両辺とも同じ変数に対する `mapTm _ (var i)` に計算されるので、パスは `refl` です。
<!--/-->

```agda
  liftTm-correct : ∀ {n} (t : Term K n) (h : BoundedTm P t)
                 → mapTm up (liftTm t h) ≡ mapTm proj t
  liftTm-correct (con c) p = cong con (down-correct c p)
  liftTm-correct (var i) _ = refl

  liftFo-correct : ∀ {n} (φ : Formula K n) (h : BoundedFo P φ)
```

<!--en-->
The formula-level statement compares the two composites `mapFo up ∘ liftFo` and `mapFo proj` applied to `φ`. An atomic formula such as `t ∈̇ u` already shows the mechanism: the goal splits into the two term goals for `t` and `u`, which the base case supplies, and `cong₂ _∈̇_` places them under the membership symbol.
<!--zh-->
公式层面的陈述比较作用于 `φ` 的两个复合 `mapFo up ∘ liftFo` 与 `mapFo proj`。像 `t ∈̇ u` 这样的原子式已经显出机制：目标拆成对 `t` 与 `u` 的两个词项目标，由基例供给，`cong₂ _∈̇_` 把它们放到属于符号之下。
<!--ja-->
論理式の水準での主張は、`φ` に適用された二つの合成 `mapFo up ∘ liftFo` と `mapFo proj` を比べるものです。`t ∈̇ u` のような原子式がすでに仕組みを示します。目標は `t` と `u` に対する二つの項の目標に分かれ、それらは基底の場合が供給し、`cong₂ _∈̇_` が所属記号の下に置きます。
<!--/-->

```agda
                 → mapFo up (liftFo φ h) ≡ mapFo proj φ
  liftFo-correct (t ∈̇ u) (ht , hu) =
    cong₂ _∈̇_ (liftTm-correct t ht) (liftTm-correct u hu)
  liftFo-correct (t ≐ u) (ht , hu) =
    cong₂ _≐_ (liftTm-correct t ht) (liftTm-correct u hu)
```

<!--en-->
Compound formulas add nothing new: each binary connective case applies `cong₂` to the symbol and the two recursive paths from the subformulas. The induction simply follows the certificate's own pairing structure, which is why the certificate was designed to mirror the syntax.
<!--zh-->
复合公式没有新内容：每个二元联结词情形都对符号施加 `cong₂`，并配上来自子公式的两条递归路径。归纳只是跟随证书自身的配对结构，这正是当初把证书设计成镜像语法的原因。
<!--ja-->
複合論理式で新しいことは何も起きません。各二項接続詞の場合は記号に `cong₂` を適用し、部分式からの二つの再帰パスを渡すだけです。帰納は証明書自身の組の構造をたどるだけで、証明書を構文の鏡として設計したのはこのためです。
<!--/-->

```agda
  liftFo-correct (φ ∧̇ ψ) (hφ , hψ) =
    cong₂ _∧̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ∨̇ ψ) (hφ , hψ) =
    cong₂ _∨̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ⇒̇ ψ) (hφ , hψ) =
```

<!--en-->
Constant-free forms are even easier. `⊥̇` maps to itself on both routes, giving `refl`; the unbounded quantifier cases each wrap one recursive path in `cong` on the quantifier symbol, since a prefix introduces no constants.
<!--zh-->
不含常元的形式更容易：`⊥̇` 在两条途径下都映到自身，给出 `refl`；无界量词情形各用 `cong` 把唯一一条递归路径包在量词符号之下，因为前缀不引入常元。
<!--ja-->
定数を含まない形式はさらに容易です。`⊥̇` はどちらの経路でも自身に写るので `refl` となり、非有界量化子の場合は前置が定数を導入しないため、唯一の再帰パスを量化子記号の `cong` で包むだけです。
<!--/-->

```agda
    cong₂ _⇒̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct ⊥̇ _ = refl
  liftFo-correct (∃̇ φ) hφ = cong ∃̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇ φ) hφ = cong ∀̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇∈ t φ) (ht , hφ) =
```

<!--en-->
A bounded quantifier combines the two kinds of case: its term path and its body path are joined by `cong₂` under the quantifier constructor, completing the induction. The declaration `Δ₀-liftFo` then turns to the second promised fact. Its statement is a transfer: given a boundedness certificate `h` for `φ` and a Δ₀ witness for `φ`, it returns a Δ₀ witness for `liftFo φ h`. The base case is the atomic witness `δ-∈`, which carries no data and survives untouched.
<!--zh-->
带界量词把两类情形合在一起：其词项路径与主体路径经 `cong₂` 在量词构造子之下合并，归纳至此完成。声明 `Δ₀-liftFo` 转向第二件被允诺的事实。其陈述是一次转移：给定 `φ` 的有界证书 `h` 与 `φ` 的一个 Δ₀ 见证，它返回 `liftFo φ h` 的一个 Δ₀ 见证。基例是原子见证 `δ-∈`，它不携带数据，原样保留。
<!--ja-->
有界量化子は二種類の場合を結合します。項のパスと本体のパスを量化子の構成子の下で `cong₂` によってつなげば帰納は完了です。宣言 `Δ₀-liftFo` はここから二つ目の事実に向かいます。その主張は転送です。`φ` の有界性の証明書 `h` と `φ` の Δ₀ 証拠を受け取り、`liftFo φ h` に対する Δ₀ 証拠を返します。基底は原子の証拠 `δ-∈` で、データを持たないためそのまま生き残ります。
<!--/-->

```agda
    cong₂ ∀̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)
  liftFo-correct (∃̇∈ t φ) (ht , hφ) =
    cong₂ ∃̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)

  Δ₀-liftFo : ∀ {n} {φ : Formula K n} (h : BoundedFo P φ) → Δ₀ φ → Δ₀ (liftFo φ h)
  Δ₀-liftFo (ht , hu) δ-∈       = δ-∈
```

<!--en-->
The recursion runs over the Δ₀ witness, not the formula; the certificate is split only to reach the sub-certificates paired with each sub-witness. Connectives rebuild their constructor from the transferred sub-witnesses, and falsity returns `δ-⊥` directly.
<!--zh-->
递归沿 Δ₀ 见证而非公式进行；证书被拆开只是为了取到与每个子见证配对的子证书。联结词情形用转移后的子见证重建其构造子，假则直接返回 `δ-⊥`。
<!--ja-->
再帰は論理式ではなく Δ₀ の証拠の上を走ります。証明書を分解するのは、各下位の証拠と組になった下位の証明書に届くためだけです。接続詞は転送された下位の証拠から自身の構成子を組み立て直し、偽は `δ-⊥` を直接返します。
<!--/-->

```agda
  Δ₀-liftFo (ht , hu) δ-≐       = δ-≐
  Δ₀-liftFo (hφ , hψ) (δ-∧ c d) = δ-∧ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-∨ c d) = δ-∨ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-⇒ c d) = δ-⇒ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo _         δ-⊥       = δ-⊥
```

<!--en-->
The bounded quantifier witnesses finish the recursion: each wraps one transferred sub-witness in `δ-∀∈` or `δ-∃∈`. Since every Δ₀ constructor has been handled, the transfer is total, and a formula's Δ₀ status is untouched by relabelling its constants.
<!--zh-->
带界量词见证完成递归：各自把一个转移后的子见证包入 `δ-∀∈` 或 `δ-∃∈`。由于每个 Δ₀ 构造子都已处理，转移是全的，公式的 Δ₀ 身份不因常元改名而改变。
<!--ja-->
有界量化子の証拠が再帰を閉じます。それぞれ転送された下位の証拠を `δ-∀∈` か `δ-∃∈` で包みます。Δ₀ の全構成子が扱われたので転送は全域的であり、論理式の Δ₀ であることは定数の改名によって損なわれません。
<!--/-->

```agda
  Δ₀-liftFo (ht , hφ) (δ-∀∈ c)  = δ-∀∈ (Δ₀-liftFo hφ c)
  Δ₀-liftFo (ht , hφ) (δ-∃∈ c)  = δ-∃∈ (Δ₀-liftFo hφ c)
```

<!--en-->
## Recap

Constant-bounded syntax packages the evidence needed by a partial constant map. Monotonicity transports that evidence along a pointwise implication of predicates. The functions `liftTm` and `liftFo`, their agreement lemmas, and `Δ₀-liftFo` then carry out certified constant relabelling while preserving the displayed syntax-level properties.
<!--zh-->
## 小结

常元有界语法打包了部分常元映射所需的证据。单调性沿谓词间的逐点蕴涵传递这些证据。随后，`liftTm` 与 `liftFo`、它们的相符性引理以及 `Δ₀-liftFo` 完成带证书的常元改名，并保持这里陈述的语法性质。
<!--ja-->
## まとめ

定数有界な構文は、部分的な定数写像に必要な証拠をまとめます。単調性は述語間の各点的含意に沿ってその証拠を移します。続いて `liftTm` と `liftFo`、それらの一致補題、`Δ₀-liftFo` が、ここで述べた構文上の性質を保ちながら、証明書付きの定数改名を実行します。
<!--/-->
