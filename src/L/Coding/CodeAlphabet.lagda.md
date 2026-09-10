<!--en-->
# The alphabet of formula codes

A statement about a constructible set `W` typically mentions members of `W`: to say, for instance, that some `x` in `W` satisfies a property, the formula carries `x` as a parameter. Internally, such parameters appear as constant symbols of a first-order language. The ambient coding of syntax, however, expects constants that are sets of the hierarchy `V ℓ`, not abstract references to members of an arbitrary set. So a bridge is needed: a language whose alphabet indexes the members of `W`, together with an embedding that gives each index its denotation as a set.

This chapter builds that bridge for a fixed `W`. The alphabet is the type of member indices of the underlying set of `W`; the embedding sends each index to the set it designates, and supplies a certificate that this set is a member of `W`. Relabeling constants along the embedding turns every term and formula over the alphabet into syntax over sets, to which the existing `V`-valued coding applies, yielding the term code `ct` and the formula code `cd`. Because the coding ignores arities, transporting a formula across an equality of arities leaves its code unchanged, as `cd-subst` records.
<!--zh-->
# 公式码的字母表

关于可构造集合 `W` 的陈述往往会提到 `W` 的成员：比如说，要断言 `W` 中某个 `x` 满足一条性质，公式就要带着 `x` 作为参数。在集合论内部，这样的参数以一阶语言的常元符号出现。然而，外围的语法编码要求常元是层级 `V ℓ` 中的集合，而不是对任意集合成员的抽象指称。因此需要一座桥：一种字母表可索引 `W` 成员的语言，连同把每个索引送到其集合指称的嵌入。

本章对固定的 `W` 搭建这座桥。字母表是 `W` 底层集合的成员索引类型；嵌入把每个索引送到它所指称的集合，并附上该集合属于 `W` 的证书。沿嵌入改标每个常元后，字母表上的每个词项与每条公式都成为以集合为常元的语法，从而适用已有的取值于 `V` 的编码，得到词项码 `ct` 与公式码 `cd`。由于该编码不查看元数，沿元数相等路径传输公式不会改变其码，这正是 `cd-subst` 所记录的事实。
<!--ja-->
# 論理式符号のアルファベット

構成可能集合 `W` についての主張は、しばしば `W` の要素に言及します。たとえば `W` に属するある `x` が性質を満たすと言うには、論理式は `x` をパラメータとして伴わなければなりません。集合論の内部では、このようなパラメータは一階言語の定数記号として現れます。しかし周囲の構文符号化は、定数が任意の集合の要素への抽象的な参照ではなく、階層 `V ℓ` の集合であることを要求します。そこで橋渡しが必要になります。アルファベットが `W` の要素を索引づけ、各インデックスに集合としての指示対象を与える埋め込みをそろえた言語です。

この章では、固定された `W` に対しその橋を構築します。アルファベットは `W` の台集合の要素へのインデックスの型であり、埋め込みは各インデックスをそれが指す集合へ送り、その集合が `W` に属することの証拠を添えます。埋め込みに沿って各定数を書き換えれば、アルファベット上のすべての項と論理式は集合を定数とする構文になり、既存の `V` 値の符号化が適用できて、項の符号 `ct` と論理式の符号 `cd` が得られます。符号化はアリティを調べないので、アリティの相等の経路に沿って論理式を輸送しても符号は変わらず、これが `cd-subst` の記録する事実です。
<!--/-->

<!--en-->
Everything in this chapter takes place at a single type-theoretic universe level `ℓ`, fixed once and used throughout. The hierarchy `V ℓ` of sets at this level is the target of the eventual coding, and the first-order language is the setting in which parameters live. The plan is uniform: given a constructible set `W`, read its members as constant symbols, name them by abstract indices, and transport each name to the set it denotes in `V ℓ`. Nothing in that plan depends on which `W` is chosen, so it is carried out for an arbitrary `W`.
<!--zh-->
本章的一切都在唯一一个类型论宇宙层次 `ℓ` 上进行，它只固定一次并贯穿全章。该层次上的集合层级 `V ℓ` 是最终编码的目标，而一阶语言则是参数所处的舞台。方案是统一的：给定可构造集合 `W`，把其成员读作常元符号，用抽象索引为它们命名，再把每个名字传输到它在 `V ℓ` 中指称的集合。这一方案不依赖于所选的 `W`，因此对任意的 `W` 通用。
<!--ja-->
この章のすべては、ただ一度だけ固定され章全体を通じて用いられる単一の型論的宇宙レベル `ℓ` の上で行われます。このレベルの集合の階層 `V ℓ` が最終的な符号化の目標であり、一階言語はパラメータが置かれる舞台です。方針は一様です。構成可能集合 `W` が与えられれば、その要素を定数記号として読み、抽象的なインデックスで名前を付け、各名前を `V ℓ` の中でそれが指す集合へ輸送します。この方針はどの `W` を選ぶかに依存しないので、任意の `W` に対して通用します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.CodeAlphabet {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The object-language syntax is generic in its alphabet. A type `Formula K n` of formulas over constants `K` and arity `n` never inspects what the constants are; it only arranges them into logical structure. Consequently, any function on the alphabet extends to a relabeling of syntax: mapping each constant through the function rewrites every occurrence while leaving connectives, quantifiers and variables untouched. Here the function will be the embedding of member indices into `V ℓ`, and the relabeled formulas will have sets as constants, which is precisely the input format of the set-valued syntax coding over the hierarchy. What remains is to choose the alphabet and the embedding so that the constants are genuinely the members of `W`.
<!--zh-->
对象语言的语法对字母表是泛的。常元类型为 `K`、元数为 `n` 的公式类型 `Formula K n` 从不查看常元本身是什么，只把它们安排进逻辑结构中。因此，字母表上的任何函数都能扩充为语法的改标：把每个常元沿该函数映射，即可改写每一处出现，而联结词、量词与变量保持不变。这里所用的函数将是把成员索引嵌入 `V ℓ` 的映射，改标后的公式以集合为常元，恰好是层级上取值于集合的语法编码所要求的输入格式。剩下的只是选好字母表与嵌入，使这些常元确实是 `W` 的成员。
<!--ja-->
対象言語の構文はアルファベットに対して汎用です。定数の型 `K` とアリティ `n` に対する論理式の型 `Formula K n` は、定数が何であるかを決して調べず、それらを論理構造へ配置するだけです。したがって、アルファベット上の任意の関数は構文の書き換えへ拡張されます。各定数をその関数を通して写せば、すべての出現が書き換えられ、論理結合子・量化子・変数はそのまま保たれます。ここで使う関数は要素のインデックスを `V ℓ` へ埋め込む写像であり、書き換え後の論理式は集合を定数とするので、階層上の集合値の構文符号化が要求する入力の形式にちょうど合います。残るのは、これらの定数が実際に `W` の要素になるようにアルファベットと埋め込みを選ぶことです。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; Term )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm )
open import V.Coding {ℓ} using ( module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open import Cubical.Foundations.Prelude using ( J; substRefl )
```

<!--en-->
Two distinctions organize the construction. First, a member of a set of the hierarchy is presented by an abstract index `q` in `⟪ a ⟫`, and the embedding `⟪ a ⟫↪` sends that index to the set it designates; the index is a name, the value `⟪ a ⟫↪ q` is the denotation in `V ℓ`, and the two roles are kept apart. Second, `W` is not an arbitrary set but an element of the carrier `S` of the constructible structure, so it comes with an underlying set `fst W` of the hierarchy and a constructibility certificate; this is what licenses reading its members as parameters of a language about constructible sets. The alphabet will be `⟪ fst W ⟫` itself, and the next section assembles these pieces into the codes `ct` and `cd`.
<!--zh-->
两个区分组织了整个构造。其一，层级的集合的成员由 `⟪ a ⟫` 中的抽象索引 `q` 呈现，嵌入 `⟪ a ⟫↪` 把该索引送到它所指称的集合；索引是名字，值 `⟪ a ⟫↪ q` 是它在 `V ℓ` 中的指称，两种角色始终分开。其二，`W` 不是任意集合，而是可构造结构载体 `S` 的元素，因而带有层级中的底层集合 `fst W` 与可构造性证书；正是这一点使我们能把它的成员读作关于可构造集合的语言的参数。字母表将取为 `⟪ fst W ⟫` 本身，下一节把这些部件装配成码 `ct` 与 `cd`。
<!--ja-->
二つの区別が構成を組織します。第一に、階層の集合の要素は `⟪ a ⟫` の抽象的なインデックス `q` によって提示され、埋め込み `⟪ a ⟫↪` はそのインデックスを指された集合へ送ります。インデックスは名前であり、値 `⟪ a ⟫↪ q` は `V ℓ` における指示対象であり、この二つの役割は終始区別されます。第二に、`W` は任意の集合ではなく、構成可能な構造の台 `S` の要素なので、階層における台集合 `fst W` と構成可能性の証拠を伴います。まさにこのおかげで、その要素を構成可能集合についての言語のパラメータとして読むことができます。アルファベットは `⟪ fst W ⟫` そのものにとられ、次の節でこれらの部品が符号 `ct` と `cd` へと組み上げられます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Embedding constants and coding syntax

The section fixes a constructible set `W` as an element of the carrier `S` and asks how to code syntax over `W` as sets. Three steps compose: extract the type `Ab` of available constant symbols, embed each symbol into the hierarchy `V ℓ` with a certificate that it lies in `W`, and then apply the set-valued coding to the relabeled terms and formulas. The final lemma disposes of a bookkeeping issue arising because formulas are indexed by their arity.
<!--zh-->
## 嵌入常元并编码语法

本节把可构造集合 `W` 取为载体 `S` 的一个元素，考察如何把 `W` 上的语法编码为集合。构造由三步复合而成：提取可用常元符号的类型 `Ab`，把每个符号嵌入层级 `V ℓ` 并附上它确实属于 `W` 的证书，然后对换标后的词项与公式施以取值于集合的编码。末尾的引理处理一个因公式按元数索引而产生的记账问题。
<!--ja-->
## 定数を埋め込んで構文を符号化する

この節では、構成可能集合 `W` を台 `S` の要素として取り、`W` 上の構文をどのように集合へ符号化するかを考えます。構成は三段階の合成です。まず利用可能な定数記号の型 `Ab` を取り出し、次に各記号を階層 `V ℓ` へ埋め込み、それが実際に `W` に属することの証拠を添え、最後に書き換え後の項と論理式に集合値の符号化を施します。最後の補題は、論理式がアリティで索引づけられることに由来する簿記上の問題を片づけます。
<!--/-->

<!--en-->
An element `W : S` packages a set of the hierarchy with structure data; `fst W` is its underlying set. The type `Ab` is then `⟪ fst W ⟫`, the type of indices for members of that set, and `ι` is the embedding `⟪ fst W ⟫↪` that sends each index to the member it designates inside `V ℓ`. So an inhabitant of `Ab` is exactly an available constant symbol, and `ι` computes its denotation as a set.
<!--zh-->
元素 `W : S` 把层级中的一个集合与结构数据打包在一起；`fst W` 是其底层集合。于是 `Ab` 就是 `⟪ fst W ⟫`，即该集合成员的索引类型，而 `ι` 是嵌入 `⟪ fst W ⟫↪`，把每个索引送到它在 `V ℓ` 中所指称的成员。因此 `Ab` 的元素恰好就是一个可用常元符号，`ι` 则算出它作为集合的指称。
<!--ja-->
要素 `W : S` は、階層のある集合を構造のデータとともに束ねたものです。`fst W` がその台集合になります。したがって `Ab` は `⟪ fst W ⟫`、つまりその集合の要素へのインデックスの型であり、`ι` は埋め込み `⟪ fst W ⟫↪` で、各インデックスを `V ℓ` 内の指された要素へ送ります。つまり `Ab` の要素こそが利用可能な定数記号であり、`ι` は集合としてのその指示対象を計算します。
<!--/-->

```agda
module Alphabet (W : S) where
  Ab : Type ℓ
  Ab = ⟪ fst W ⟫

  ι : Ab → V ℓ
  ι = ⟪ fst W ⟫↪
```

<!--en-->
The membership certificate `ι∈` says that for every constant symbol `q`, the set `ι q` genuinely is a member of `fst W`; it is read off from the library's equivalence between membership and the classified membership relation `∈ₛ`. With the alphabet in place, `cd` and `ct` are now almost forced: `mapFo ι` and `mapTm ι` rewrite a formula or term by replacing each constant `con q` with `con (ι q)`, and the brackets `⌜_⌝` and `⌜_⌝ᵗ` from the hierarchy coding then package the result as a set. The logical skeleton of the formula survives the relabeling untouched, which is exactly why the coding can be reused.
<!--zh-->
隶属证书 `ι∈` 说明：对每个常元符号 `q`，集合 `ι q` 确实是 `fst W` 的成员；它由库中隶属关系与带分类的隶属关系 `∈ₛ` 之间的等价直接读出。字母表就位后，`cd` 与 `ct` 几乎是被逼出来的：`mapFo ι` 与 `mapTm ι` 把每处常元 `con q` 替换为 `con (ι q)` 来改写公式或词项，随后层级编码的括号 `⌜_⌝` 与 `⌜_⌝ᵗ` 把所得结果打包为集合。改标后公式的逻辑骨架原样保留，这正是能够复用该编码的原因。
<!--ja-->
所属の証拠 `ι∈` は、各定数記号 `q` に対して集合 `ι q` が実際に `fst W` の要素であることを述べます。これは、所属関係と分類つきの所属関係 `∈ₛ` との間のライブラリの同値からそのまま読み取れます。アルファベットが整うと、`cd` と `ct` はほとんど自動的に決まります。`mapFo ι` と `mapTm ι` が各定数 `con q` を `con (ι q)` に置き換えて論理式や項を書き換え、階層符号化の括弧 `⌜_⌝` と `⌜_⌝ᵗ` がその結果を集合としてまとめるのです。書き換えの後も論理式の論理的な骨格はそのまま保たれるので、既存の符号化をそのまま再利用できます。
<!--/-->

```agda

  ι∈ : (q : Ab) → ⟨ ι q ∈ fst W ⟩
  ι∈ q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)

  cd : ∀ {n} → Formula Ab n → V ℓ
  cd ψ = VCode.⌜ mapFo ι ψ ⌝

  ct : ∀ {n} → Term Ab n → V ℓ
```

<!--en-->
A formula of type `Formula Ab n` carries an arity `n`, and in dependent type theory that index is part of the type. If a proof later needs `n` and `n'` to be equal, it transports the formula along a path `e : n ≡ n'`, and the transported formula is a different inhabitant syntactically even when the underlying formula is the same. The lemma `cd-subst` shows that this makes no difference for coding: `cd` applied to the transported formula equals `cd` applied to the original. The proof is by `J` on `e`, where the reflexive case holds because transporting along `refl` is the identity and `substRefl` makes that reduction explicit, leaving `cong cd` to equate the two applications.
<!--zh-->
类型 `Formula Ab n` 的公式带有元数 `n`，而在依值类型论中该索引是类型的一部分。若某个证明稍后需要 `n` 与 `n'` 相等，它会沿路径 `e : n ≡ n'` 对公式作传输；传输后的公式在语法上是另一个居民，即便底层的公式未变。引理 `cd-subst` 表明这对编码毫无影响：作用于传输后公式的 `cd` 等于作用于原公式的 `cd`。证明对 `e` 使用 `J`，自反情形成立是因为沿 `refl` 的传输是恒等，而 `substRefl` 把这一化简显式化，剩下由 `cong cd` 把两次作用等同起来。
<!--ja-->
型 `Formula Ab n` の論理式はアリティ `n` を伴い、依存型理論ではこのインデックスが型の一部です。後の証明で `n` と `n'` の相等が必要になると、経路 `e : n ≡ n'` に沿って論理式を輸送します。輸送された論理式は、元の論理式が同じでも、構文の上では別の要素です。補題 `cd-subst` は、これが符号化には何の影響も与えないことを示します。輸送後の論理式に適用した `cd` は、元の論理式に適用した `cd` と等しいのです。証明は `e` に対する `J` によるもので、反射的な場合は `refl` に沿った輸送が恒等写像であり、`substRefl` がこの簡約を明示するため成立し、残りは `cong cd` で二つの適用を結びます。
<!--/-->

```agda
  ct t = VCode.⌜ mapTm ι t ⌝ᵗ

  cd-subst : ∀ {n n'} (e : n ≡ n') (ψ : Formula Ab n) → cd (subst (Formula Ab) e ψ) ≡ cd ψ
  cd-subst {n} e ψ = J (λ n' e' → cd (subst (Formula Ab) e' ψ) ≡ cd ψ)
    (cong cd (substRefl {B = Formula Ab} ψ)) e
```

<!--en-->
## Recap

`Alphabet W` regards the members of a constructible set `W` as the constant symbols of a first-order language, embeds each of them into the ambient hierarchy with the certificate `ι∈`, and returns the resulting set codes of terms and formulas through `ct` and `cd`. Because the coding never inspects the arity, `cd-subst` guarantees that transporting a formula across an equality of arities does not change its code.
<!--zh-->
## 小结

`Alphabet W` 把可构造集合 `W` 的成员看作一阶语言的常元符号，将每个成员嵌入外围层级并附上证书 `ι∈`，再通过 `ct` 与 `cd` 给出词项与公式所得的集合码。由于编码从不查看元数，`cd-subst` 保证了沿元数相等的路径传输公式不会改变其码。
<!--ja-->
## まとめ

`Alphabet W` は構成可能集合 `W` の要素を一階言語の定数記号とみなし、それぞれを証拠 `ι∈` とともに周囲の階層へ埋め込み、`ct` と `cd` によって項と論理式の集合としての符号を与えます。符号化がアリティを決して調べないため、`cd-subst` は、アリティの相等の経路に沿って論理式を輸送してもその符号が変わらないことを保証します。
<!--/-->
