<!--en-->
# The axiom of infinity in L

Inside `L`, the constructively defined chain `numeralL`{.Agda} provides one internal numeral for each natural number. A chain of separate sets is not yet an infinite set: the axiom of infinity asks for one constructible set whose members are exactly the numerals. This chapter exhibits that set and, in the same stroke, identifies the classical dependency used to place the candidate set in the constructible hierarchy: knowing at which stage of the constructible hierarchy an ordinal such as ω appears is a comparison of ordinals, the imported stage theorem receives the module parameter `lem` because its proof uses that comparison.
<!--zh-->
# L 中的无穷公理

`L` 内构造性定义的数码链 `numeralL`{.Agda} 为每个自然数给出一个内部数码。但一条由各自分离的集合组成的链还不是无穷集合：无穷公理要求一个可构造集合，其成员恰为诸数码。本章给出这个集合，并顺带指出把候选集合放进可构造层级时所用的经典依赖：所导入的层定理依赖序数比较，因此以模块参数 `lem` 为参数。
<!--ja-->
# L における無限公理

`L` の内部で構成的に定義された数項列 `numeralL`{.Agda} は、各自然数に一つの内部数項を与えます。しかし、互いに別々の集合からなる数項列は、まだ無限集合ではありません。無限公理が求めるのは、要素が数項ちょうどである一つの構成可能集合です。この章ではその集合を示し、あわせて候補の集合を構成可能階層へ置くために用いる古典的依存関係を明らかにします。ω のような順序数が構成可能階層のどの段階に現れるかを知ることは順序数の比較であり、インポートされた段階定理はその比較を用いるため、モジュールパラメータ `lem` を受け取ります。
<!--/-->

<!--en-->
The module takes a single assumption, `lem : LEM (ℓ-suc ℓ)`, a decision procedure for propositions at one level above the working level ℓ. Everything the chapter needs is either constructive or derived from this one parameter, so the later proofs can be read with a precise account of which steps are classical.
<!--zh-->
模块只带一个假设 `lem : LEM (ℓ-suc ℓ)`，即比工作层级 ℓ 高一层级的命题的判定。本章所需的一切，要么是构造性的，要么由这一个参数导出，因此后文的证明可以带着「哪些步骤是经典的」这一精确账目来读。
<!--ja-->
このモジュールが取る仮定は `lem : LEM (ℓ-suc ℓ)` の一つだけです。これは作業レベル ℓ の一つ上のレベルの命題に対する判定です。本章で必要なものは、構成的であるか、この一つのパラメータから導かれるかのどちらかなので、以降の証明は、どの段階が古典的かという正確な勘定をもって読めます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Infinity {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The ambient hierarchy supplies `ω` and its successor `sucV`, while `numeralL-fst` relates each internal numeral to the corresponding member of `ω`. The stage theorem `ord∈Lset-suc`, instantiated with `lem`, places an ordinal at its successor stage. This is the sole point at which the proof below invokes a result parameterized by excluded middle.
<!--zh-->
周遭集合层级提供 `ω` 与后继 `sucV`，而 `numeralL-fst` 把每个内部数码同 `ω` 的相应成员联系起来。以 `lem` 实例化的层定理 `ord∈Lset-suc` 把序数置于其后继层。下述证明只在这里调用以排中律为参数的结果。
<!--ja-->
周囲の集合階層は `ω` と後者 `sucV` を与え、`numeralL-fst` は各内部数項を `ω` の対応する要素に結びつけます。`lem` で具体化した段階定理 `ord∈Lset-suc` は、順序数をその後者段階に置きます。以下の証明が排中律をパラメータとする結果を用いるのはこの箇所です。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
```

<!--en-->
Propositional truncation expresses mere existence: `∣_∣₁`{.Agda} places a given witness inside that truncation. The operation `⇔toPath`{.Agda} converts two implications between truth values into a path between those truth values, which is the form required by the set specification.
<!--zh-->
命题截断表达单纯存在：`∣_∣₁`{.Agda} 把给定见证置于这一截断中。运算 `⇔toPath`{.Agda} 把真值间的两个蕴涵转换为真值间的路径，这正是集合规格所要求的形式。
<!--ja-->
命題的切り詰めは単なる存在を表し、`∣_∣₁`{.Agda} は与えられた証人をその切り詰めに入れます。`⇔toPath`{.Agda} は真理値間の二つの含意を真理値間のパスに変換し、集合の仕様が要求する形を与えます。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ} using ( uniqueL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
Truth values here are `hProp` packages, and their indexed disjunction `⋁`{.Agda} expresses mere existence over a carrier. For the constructible structure `𝒮ʟ`, `∈ˢ`{.Agda} denotes membership and `≈ˢ`{.Agda} denotes structural equality, whose underlying equality is equality of the ambient sets.
<!--zh-->
这里的真值是 `hProp` 封装；其索引析取 `⋁`{.Agda} 表达沿某个载体的单纯存在。对可构造结构 `𝒮ʟ`，`∈ˢ`{.Agda} 表示属于，`≈ˢ`{.Agda} 表示结构相等，其底层等式是周遭集合之间的等式。
<!--ja-->
ここでの真理値は `hProp` の組であり、その添字付き選言 `⋁`{.Agda} は、ある担体にわたる単なる存在を表します。構成可能構造 `𝒮ʟ` では、`∈ˢ`{.Agda} は所属を、`≈ˢ`{.Agda} は構造の等しさを表し、その基礎にある等式は周囲の集合の等式です。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
```

<!--en-->
Finally `SetOf`{.Agda} names the type of realizers of a class: a constructible set together with a proof that, for every element, its membership truth value equals the class's value. The infinity field of the model record will ask for contractibility of this type, and `uniqueL` will supply that from a single realizer.
<!--zh-->
最后，`SetOf`{.Agda} 指名一个类的实现者类型：一个可构造集合，连同「对每个元素，其属于真值等于该类的值」的证明。模型 record 的无穷字段将要求这个类型具有可缩性，而 `uniqueL` 会从单独一个实现者提供它。
<!--ja-->
最後に、`SetOf`{.Agda} はクラスの実現者の型を指します。すなわち、構成可能集合と、すべての要素についてその所属の真理値がクラスの値に等しいことの証明を組にしたものです。モデル record の無限フィールドはこの型の可縮性を要求し、`uniqueL` が単独の実現者からそれを供給します。
<!--/-->

```agda

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )
```

<!--en-->
## Collecting the chain

The ambient `ω`, whose members are the library numerals, is the natural candidate. The proof that it is constructible applies `ord∈Lset-suc` to `ω`; this imported stage theorem is instantiated with the module parameter `lem`. The definitions of the numeral chain and its membership specification do not themselves invoke that parameter.
<!--zh-->
## 收集这条链

周遭集合 `ω` 的成员是库中的数码，因此它是自然的候选。其可构造性证明把 `ord∈Lset-suc` 应用于 `ω`；这条导入的层定理以模块参数 `lem` 实例化。数码链及其成员规格的定义本身不调用该参数。
<!--ja-->
## 数項列を集合に集める

周囲の集合 `ω` の要素はライブラリの数項なので、これが自然な候補です。その構成可能性の証明は `ord∈Lset-suc` を `ω` に適用し、このインポートされた段階定理をモジュールのパラメータ `lem` で具体化します。数項列とその要素の仕様の定義自体は、このパラメータを呼び出しません。
<!--/-->

<!--en-->
The statement `ω∈L` has the truncated form prescribed by the definition of `isL`. A witness before truncation is the stage `sucV ω`: `ω-ord` says that `ω` is an ordinal, `suc-ord` says that `sucV ω` is again an ordinal, and `ord∈Lset-suc` places `ω` at that stage. The element `ωʟ` pairs the ambient set `ω` with this constructibility proof, so `x ∈ˢ ωʟ` is membership in its underlying ambient set.
<!--zh-->
命题 `ω∈L` 具有 `isL` 定义所规定的截断形式。截断前的一个见证是层 `sucV ω`：`ω-ord` 说明 `ω` 是序数，`suc-ord` 说明其冯·诺伊曼后继 `sucV ω` 仍是序数，而 `ord∈Lset-suc` 把 `ω` 置于该层。元素 `ωʟ` 把周遭集合 `ω` 与这一可构造性证明配对，因此 `x ∈ˢ ωʟ` 就是对其底层周遭集合的属于关系。
<!--ja-->
命題 `ω∈L` は、`isL` の定義が定める切り詰められた形を取ります。切り詰める前の証人の一つは段階 `sucV ω` です。`ω-ord` は `ω` が順序数であることを、`suc-ord` はそのフォン・ノイマン後者 `sucV ω` も順序数であることを述べ、`ord∈Lset-suc` が `ω` をその段階に置きます。要素 `ωʟ` は周囲の集合 `ω` とこの構成可能性の証明を組にするので、`x ∈ˢ ωʟ` はその基礎にある周囲の集合への所属です。
<!--/-->

```agda
ω∈L : ⟨ isL ω ⟩
ω∈L = ∣ sucV ω , (suc-ord ω-ord , ord∈Lset-suc ω ω-ord) ∣₁

ωʟ : S
ωʟ = ω , ω∈L
```

<!--en-->
It remains to verify that the members of `ωʟ` are exactly the internal numerals. The class `isNumeralL` says of an element `x` that it is structurally equal to the chain's `n`-th link for some natural number `n`; as an indexed disjunction it merely asserts that some index works, without choosing one. The specification `ω-specL` then proves that membership in `ωʟ` and `isNumeralL` agree pointwise as truth values, and `hasInfinityL` promotes the realizer to the contractibility the axiom field requires. Both directions of the specification run through the same two ingredients: the ambient characterization of membership in `ω`, and the chain's projection equation `numeralL-fst`.
<!--zh-->
余下的工作是核实 `ωʟ` 的成员恰是内部数码。类 `isNumeralL` 对元素 `x` 说：存在某个自然数 `n`，使 `x` 结构上等于链的第 `n` 节；作为索引析取，它仅仅断言某个下标可行，而不选定任何一个。规格 `ω-specL` 接着证明，属于 `ωʟ` 与 `isNumeralL` 作为真值逐点一致；`hasInfinityL` 再把这个实现者提升为公理字段所要求的可缩性。规格的两个方向都经过同样两件素材：`ω` 中属于关系的周遭刻画，以及链的投影方程 `numeralL-fst`。
<!--ja-->
残る作業は、`ωʟ` の要素が内部の数項ちょうどであることを確かめることです。クラス `isNumeralL` は要素 `x` について、ある自然数 `n` に対して `x` が数項列の第 `n` 項と構造的に等しいと述べます。索引付き選言として、これはどれかの添字が機能することを単に主張するのであって、ひとつを選ぶことはしません。仕様 `ω-specL` は次に、`ωʟ` への所属と `isNumeralL` が真理値として各点で一致することを証明し、`hasInfinityL` がこの実現者を、公理フィールドが要求する可縮性へ持ち上げます。仕様の両方向は、同じ二つの素材、すなわち `ω` への所属の周囲での特徴づけと、数項列の射影方程式 `numeralL-fst` を通ります。
<!--/-->

<!--en-->
The class `isNumeralL` disjoins, over the carrier `Lift ℕ`, the family of propositions `x ≈ˢ numeralL (lower n)`. The `Lift` deserves a word: `⋁`{.Agda} requires its carrier to live at the working level, while `ℕ` lives at `ℓ-zero`, and lifting is a pure level adjustment carrying exactly the same elements, with `lower` recovering the plain index. The specification `ω-specL` states the goal as a path between truth values, `(x ∈ˢ ωʟ) ≡ isNumeralL x`, and `⇔toPath` reduces proving that path to proving the two implications.
<!--zh-->
类 `isNumeralL` 沿载体 `Lift ℕ` 析取命题族 `x ≈ˢ numeralL (lower n)`。这里的 `Lift` 值得一提：`⋁`{.Agda} 要求载体住在工作层级，而 `ℕ` 住在 `ℓ-zero`；提升是纯粹的对齐层级的调整，恰带同样的元素，`lower` 取回普通下标。规格 `ω-specL` 把目标写成真值之间的一条路径 `(x ∈ˢ ωʟ) ≡ isNumeralL x`，而 `⇔toPath` 把这条路径的证明化归为两个蕴涵的证明。
<!--ja-->
クラス `isNumeralL` は、担体 `Lift ℕ` の上で、命題の族 `x ≈ˢ numeralL (lower n)` を選言します。`Lift` に一言ふれておきます。`⋁`{.Agda} は担体が作業レベルに住むことを要求しますが、`ℕ` は `ℓ-zero` に住みます。lift はまったく同じ要素を持つ純粋なレベル調整であり、`lower` が普通の添字を取り戻します。仕様 `ω-specL` は目標を真理値の間のパス `(x ∈ˢ ωʟ) ≡ isNumeralL x` として述べ、`⇔toPath` はこのパスの証明を二つの含意の証明に帰着させます。
<!--/-->

```agda
isNumeralL : S → Ω
isNumeralL x = ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralL (lower n))

ω-specL : (x : S) → (x ∈ˢ ωʟ) ≡ isNumeralL x
ω-specL x = ⇔toPath
  (PT.map (λ { (k , p) → lift (lower k)
```

<!--en-->
Each direction maps witnesses while they remain inside propositional truncation. Forward, write the lifted index as `k : Lift ℕ` and set `n = lower k`. Ambient membership in `ω` supplies `p : # n ≡ fst x`; then `sym p ∙ sym (numeralL-fst n)` proves `x ≈ˢ numeralL n`. Backward, from `q : fst x ≡ fst (numeralL n)`, the path `sym (q ∙ numeralL-fst n) : # n ≡ fst x` gives the required ambient membership witness. Thus `ωʟ` has exactly the internal numerals as members. Finally, `uniqueL` makes the explicit realizer `(ωʟ , ω-specL)` the center of a contraction and gives a path from that center to every other realizer, proving `SetOf isNumeralL` contractible.
<!--zh-->
两个方向都在命题截断内部映射见证。正向把提升后的下标写成 `k : Lift ℕ`，并令 `n = lower k`。`ω` 中的周遭属于关系给出 `p : # n ≡ fst x`，于是 `sym p ∙ sym (numeralL-fst n)` 证明 `x ≈ˢ numeralL n`。反向从 `q : fst x ≡ fst (numeralL n)` 构造路径 `sym (q ∙ numeralL-fst n) : # n ≡ fst x`，得到所需的周遭属于见证。因此 `ωʟ` 的成员恰为内部数码。最后，`uniqueL` 以显式实现者 `(ωʟ , ω-specL)` 为可缩中心，并给出从该中心到任意其他实现者的路径，从而证明 `SetOf isNumeralL` 可缩。
<!--ja-->
両方向とも、証人を命題的切り詰めの内部に保ったまま写します。順方向では、持ち上げられた添字を `k : Lift ℕ` とし、`n = lower k` と置きます。`ω` への周囲の所属から `p : # n ≡ fst x` が得られ、`sym p ∙ sym (numeralL-fst n)` が `x ≈ˢ numeralL n` を証明します。逆方向では、`q : fst x ≡ fst (numeralL n)` からパス `sym (q ∙ numeralL-fst n) : # n ≡ fst x` を作り、必要な周囲の所属の証人を得ます。したがって `ωʟ` の要素は内部数項ちょうどです。最後に `uniqueL` は明示的な実現者 `(ωʟ , ω-specL)` を可縮性の中心とし、その中心から任意の他の実現者へのパスを与えて、`SetOf isNumeralL` が可縮であることを証明します。
<!--/-->

```agda
             , (sym p ∙ sym (numeralL-fst (lower k))) }))
  (PT.map (λ { (n , q) → lift (lower n)
             , (sym (q ∙ numeralL-fst (lower n))) }))

hasInfinityL : isContr (SetOf isNumeralL)
hasInfinityL = uniqueL isNumeralL (ωʟ , ω-specL)
```

<!--en-->
## Recap

The constructible set `ωʟ` collects exactly the chain `numeralL`{.Agda}. The explicit realizer and extensional uniqueness give the contractibility required by the infinity field. The proof uses the excluded-middle parameter through `ord∈Lset-suc` when establishing the constructibility of `ω`; the membership specification itself follows from the two projection paths above.
<!--zh-->
## 小结

可构造集合 `ωʟ` 恰好收集数码链 `numeralL`{.Agda}。显式实现者与外延唯一性给出无穷字段所要求的可缩性。证明在确立 `ω` 的可构造性时通过 `ord∈Lset-suc` 使用排中律参数；成员规格本身则由上述两个投影路径得到。
<!--ja-->
## まとめ

構成可能集合 `ωʟ` は数項列 `numeralL`{.Agda} をちょうど集めます。明示的な実現者と外延的一意性が、無限公理のフィールドに必要な可縮性を与えます。証明は `ω` の構成可能性を示す際に `ord∈Lset-suc` を通じて排中律のパラメータを使い、要素の仕様そのものは上の二つの射影パスから従います。
<!--/-->
