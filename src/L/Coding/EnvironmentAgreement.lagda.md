<!--en-->
# Agreement of environment sets

The satisfaction clauses need, inside `L`, a single set containing exactly the environments of a given length over a given base set. Earlier chapters supplied two separate pieces: `envSetAt`, the formula characterizing such a set by its members, and `envSet B m`, the set constructed in the previous chapter. A set satisfies the description exactly when each of its members is, as a set, the graph of a length-`m` environment over the base. This chapter proves that the description and the constructed set agree, and the agreement has two readings. A set that a satisfaction judgment has placed at the description's set slot has precisely the members of the constructed set; and the constructed set itself satisfies the description, so a clause that binds its own base and length may fill its slots with the constructed data and quote the description.

Both readings rest on one object, the environment recovered from a member. The four internal clauses, single-valuedness, a numeral domain, values in the base, and pairs made of numerals and base members, say of a set that it is such a graph; from them the previous chapter recovered the assigning function and identified the set with the canonical graph of that function. Here every step reduces to running that recovery in one direction or the other, and to the transport lemma that carries a satisfaction of the environment clause between environments whose named slots agree.
<!--zh-->
# 环境集的一致性

满足关系的诸子句需要在 `L` 内部有一个集合，恰好收齐给定基集合上给定长度的全部环境。较早的章节分别给出了两项材料：按成员刻画这种集合的公式 `envSetAt`，以及上一章构造的集合 `envSet B m`。一个集合满足该描述，当且仅当其成员作为集合恰是基上长度 `m` 环境的图。本章证明这条描述与已构造的集合彼此一致，而一致有两个读法。凡被某个满足判断放到描述之集合槽位上的集合，其成员恰为已构造集合的成员；已构造的集合自身也满足该描述，于是绑定自己的基与长度的子句可以先把已构造的数据填入槽位，再引用这条描述。

两种读法都落在同一个对象上：从成员恢复出的环境。四条内部子句，单值性、以数码为定义域、取值落在基中、以及由数码与基中成员组成的对，说明一个集合正是这样的图；上一章由此恢复了那个赋值函数，并把该集合与其典范图等同起来。本章的每一步都归结为沿某个方向运行这一恢复，再加上一条搬运引理：当两个环境中被点名的槽位一致时，它把环境子句的满足关系从一个环境搬到另一个环境。
<!--ja-->
# 環境の集合の一致

充足関係の節には、`L` の内部で、ある基礎集合の上の与えられた長さの環境をちょうどすべて集めた一つの集合が必要である。これまでの章は二つの材料を別々に与えた。要素によってそのような集合を特徴づける論理式 `envSetAt` と、前章で構成した集合 `envSet B m` である。ある集合がこの記述を満たすのは、その各要素が集合として、基礎の上の長さ `m` の環境のグラフであるとき、かつそのときである。本章は、記述と構成済みの集合が一致することを証明する。一致には二つの読み方がある。充足の判断によって記述の集合スロットに置かれた集合は、構成済みの集合とちょうど同じ要素を持ち、また構成済みの集合それ自体が記述を満たすので、自分の基礎と長さを束縛する節は、構成済みのデータでスロットを埋めてから記述を引用できる。

どちらの読み方も、要素から復元された環境という一つの対象の上で行われる。単値性、数項による定義域、基礎への所属、そして数項と基礎の要素からなる対、という四つの内部の節が、ある集合がこのようなグラフであることを述べる。前の章はそこから割り当ての関数を復元し、その集合を関数の正準なグラフと同一視した。本章の各段階は、この復元をいずれかの方向に走らせることと、名指されたスロットの一致する環境の間で環境の節の充足を運ぶ輸送の補題とに帰着する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
The book’s standing options remain in force. This chapter’s only nonconstructive input appears explicitly as the parameter `lem` below.
<!--zh-->
全书的常设选项继续生效。本章唯一的非构造性输入明确表现为下方的参数 `lem`。
<!--ja-->
本書の常設のオプションは引き続き有効である。本章で唯一用いる非構成的な入力は、下のパラメータ `lem` として明示される。
<!--/-->

```agda

open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The basic vocabulary arrives as a whole, as the Prelude arranged. Excluded middle enters as data rather than as an option, and the chapter receives it as a parameter.
<!--zh-->
基础词汇按《基础词汇》的安排整体引入。排中律不作为选项，而作为数据进入，本章以参数的形式接收它。
<!--ja-->
基礎語彙は「基礎語彙」の章の配置どおり全体として導入される。排中律はオプションとしてではなくデータとして現れ、本章はこれをパラメータとして受け取る。
<!--/-->

```agda

module L.Coding.EnvironmentAgreement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The module parameter is an instance of excluded middle at level `ℓ-suc ℓ`, the level at which the satisfaction statements of the two structures live. It is forwarded to the chapter whose constructed set this chapter quotes.
<!--zh-->
模块参数是层级 `ℓ-suc ℓ` 上的排中律实例，正是两个结构的满足陈述所在的层级。它被转交给本章所引用的、构造环境集的那一章。
<!--ja-->
モジュールパラメータはレベル `ℓ-suc ℓ` の排中律の実例で、二つの構造の充足の主張の住むレベルに一致する。これは、この章が引用する環境の集合を構成した章へそのまま渡される。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
```

<!--en-->
Two structures interpret the language, and the chapter moves between them. The ambient structure `𝒮ᵥ` is the hierarchy itself; the inner structure `𝒮ʟ` restricts it to the constructible sets, the class named by `isL`. The class is transitive, recorded by `isL-trans`, and the absoluteness machinery is imported to work over exactly this pair.
<!--zh-->
解释语言的有两个结构，本章在它们之间移动。周遭结构 `𝒮ᵥ` 就是层级自身；内层结构 `𝒮ʟ` 把它限制到可构造集，即 `isL` 所指的类。该类是传递的，由 `isL-trans` 记录；绝对性机制被引入，恰好在这一对结构上工作。
<!--ja-->
言語を解釈する構造は二つであり、本章はその間を行き来する。周囲の構造 `𝒮ᵥ` は階層そのものであり、内側の構造 `𝒮ʟ` はそれを構成可能な集合のクラス `isL` に制限したものである。このクラスは推移的であり、`isL-trans` がそれを記録する。絶対性の機構は、まさにこの組の上で働くために導入される。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( envOverAt; envOverAt-transport )
open import L.Coding.Expressions {ℓ} using ( envSetAt; extAt-out; extAt-in; extAt-in-both; numL )
```

<!--en-->
Two formulas and their readers do the chapter's work. The environment clause `envOverAt` says that the candidate graph is single-valued, has exactly the set in the named domain slot as its domain, takes values in the named base set, and contains only pairs drawn from those two sets; the transport lemma moves a satisfaction of this clause between environments whose named slots agree. The extensional description `envSetAt` says of a set that its members are exactly the environments, in the form of two universally quantified implications, and the three readers unpack those implications in either direction.
<!--zh-->
两条公式及其读式承担本章的工作。环境子句 `envOverAt` 说候选图是单值的，其定义域恰为指定定义域槽位中的集合，其取值属于指定基集合，且只含由这两个集合的成员组成的对；搬运引理则在被点名的槽位一致的环境之间移动这条子句的满足。外延描述 `envSetAt` 以两条全称蕴含的形式说：一个集合的成员恰好是那些环境；三条读式按任一方向拆开这两条蕴含。
<!--ja-->
二つの論理式とその読み方が本章の仕事を担う。環境の節 `envOverAt` は、候補のグラフが単値であり、その定義域が指定された定義域スロットの集合とちょうど一致し、値が指定された基礎集合に属し、その二つの集合の要素からなる対だけを含むことを述べ、輸送の補題は、名指されたスロットの一致する環境の間でこの節の充足を運ぶ。外延的な記述 `envSetAt` は、二つの全称含意の形で、ある集合の要素がちょうどそれらの環境であることを述べ、三つの読み方がこれらの含意をどちらの向きにもほどく。
<!--/-->

```agda
open import L.Coding.EnvironmentSet {ℓ} lem
  using ( envSet; envSet-in; envSet-out; envS; envOver; module Recover )
```

<!--en-->
From the previous chapter come the constructed set `envSet`, its two membership lemmas, the canonical graph element `envS`, the environment clause `envOver` satisfied at its own canonical environment, and the recovery module that reads an environment off the four clauses and identifies the set with that environment's graph.
<!--zh-->
来自上一章的有：已构造的集合 `envSet`、它的两条隶属引理、典范图元素 `envS`、在其自身典范环境处满足的环境子句 `envOver`，以及恢复模块，后者从四条子句读出一个环境，并把该集合与那个环境的图等同起来。
<!--ja-->
前の章から来るのは、構成済みの集合 `envSet`、その二つの所属の補題、正準なグラフの要素 `envS`、みずからの正準な環境で満たされる環境の節 `envOver`、そして復元のモジュールである。復元のモジュールは四つの節から環境を読み取り、その集合をその環境のグラフと同一視する。
<!--/-->

```agda

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
```

<!--en-->
Decoding membership in an environment set into a representing environment returns only a truncated witness, while the target satisfaction and membership statements are propositions. The ambient numerals `# m` fill the length slots.
<!--zh-->
从环境集的隶属解码出表示它的环境时，只得到截断见证；目标中的满足与隶属陈述则都是命题。周遭数码 `# m` 填充长度槽位。
<!--ja-->
環境の集合への所属からそれを表す環境を復号すると、切り詰められた証人だけが得られる。一方、目標となる充足と所属の主張はいずれも命題である。周囲の数項 `# m` が長さのスロットを埋める。
<!--/-->

```agda

open hPropStructure 𝒮ʟ
```

<!--en-->
Opening the inner structure fixes the satisfaction notation used throughout: members of its carrier, its membership, and satisfaction judgments read in `L`.
<!--zh-->
打开内层结构即固定全章使用的满足记号：其载体的成员、其隶属关系，以及在 `L` 中读出的满足判断。
<!--ja-->
内側の構造を開くと、全章で使う充足の記法が固定される。その台の要素、その所属関係、そして `L` の中で読まれる充足の判断である。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
The absoluteness module is instantiated over the transitive class of constructible sets, and its inner satisfaction relation is renamed to the plain `_⊨_`, since this chapter reads every formula over `L` and no other reading competes with it.
<!--zh-->
绝对性模块在可构造集这个传递类上实例化，其内层满足关系被改名为朴素的 `_⊨_`，因为本章读出的每条公式都在 `L` 之上，没有别的读法与它竞争。
<!--ja-->
絶対性のモジュールは構成可能な集合という推移的クラスの上で実例化され、その内側の充足関係には平易な `_⊨_` の名が与えられる。本章が読む論理式はすべて `L` の上のものであり、それと競う読み方はほかにないからである。
<!--/-->

<!--en-->
## From the description to membership

The first module fixes a base set `B`, an environment `γ` of some length `k`, three of its slots, a length `m`, and two equations saying that the length slot is filled by the numeral of `m` and the base slot by `B`. Its hypothesis is that `γ` satisfies the description with the set slot at `Ei`. The conclusion is an agreement of members: the set named at `Ei` and the constructed `envSet B m` contain exactly the same sets.
<!--zh-->
## 从描述得到隶属关系

第一个模块固定基集合 `B`、某个长度 `k` 的环境 `γ`、它的三个槽位、一个长度 `m`，以及两条等式，后者说明长度槽位由 `m` 的数码填充、基槽位由 `B` 填充。其前提是 `γ` 满足以 `Ei` 为集合槽位的描述。结论是成员的一致：`Ei` 处所指名的集合与已构造的 `envSet B m` 恰好包含相同的集合。
<!--ja-->
## 記述から所属関係へ

最初のモジュールは、基礎集合 `B`、長さ `k` の環境 `γ`、その三つのスロット、長さ `m`、そして二つの等式を固定する。等式は、長さのスロットが `m` の数項で、基礎のスロットが `B` で埋められていることを述べる。前提は、`γ` が集合スロットを `Ei` に置いた記述を満たすことである。結論は要素の一致である。`Ei` の指す集合と構成済みの `envSet B m` は、ちょうど同じ集合を含む。
<!--/-->

<!--en-->
Both directions run on the same two ingredients. The recovery module reads an environment off the four clauses and identifies the set it came from with the canonical graph of that environment; the transport lemma carries a satisfaction of the environment clause between environments whose named slots agree, along exactly those naming equations. Neither direction re-proves the description or the construction.
<!--zh-->
两个方向都只依赖同样的两件材料。恢复模块从四条子句读出一个环境，并把来源集合与那个环境的典范图等同起来；搬运引理沿那几条命名等式，把环境子句的满足在被点名的槽位一致的环境之间搬运。两个方向都不重新证明描述，也不重新证明构造。
<!--ja-->
どちらの方向も、同じ二つの材料の上を走る。復元のモジュールは四つの節から環境を読み取り、その出所の集合をその環境の正準なグラフと同一視し、輸送の補題は、名指されたスロットの一致する環境の間を、まさにそれらの名指しの等式に沿って環境の節の充足を運ぶ。どちらの方向も、記述や構成を証明し直すことはない。
<!--/-->

```agda
private
  nn : ℕ → S
  nn j = # j , numL j
```

<!--en-->
The length slot is filled by a numeral, and the numeral must itself be an element of `L`. The helper `nn` forms it: the ambient von Neumann numeral `# j` paired with its constructibility proof.
<!--zh-->
长度槽位由一个数码填充，而数码本身必须是 `L` 的元素。辅助定义 `nn` 造出它：周遭的冯·诺伊曼数码 `# j` 连同其可构造性证明组成的对。
<!--ja-->
長さのスロットは数項で埋められ、その数項自身も `L` の要素でなければならない。補助定義 `nn` がこれを作る。周囲のフォン・ノイマン数項 `# j` に、その構成可能性の証明を対にしたものである。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda

module Ambient (B : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k) (m : ℕ)
  (qd : fst (lookup di γ) ≡ # m) (qb : fst (lookup bi γ) ≡ fst B)
  (hE : ⟨ γ ⊨ envSetAt Ei di bi ⟩) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
The module gathers the data of one instance of the question. `B` is the base set, `γ` an environment of length `k`, and three of its slots are named: `Ei` holds the candidate set, `di` holds the numeral of the length, `bi` holds the base. The equations `qd` and `qb` say that these two slots really are filled by the numeral of `m` and by `B`, and `hE` says that `γ` satisfies the description with the set slot at `Ei`. Under these data, the set at `Ei` and `envSet B m` are shown to have the same members.
<!--zh-->
模块汇集了该问题一个实例的全部数据。`B` 是基集合，`γ` 是长度 `k` 的环境，其中三个槽位被点名：`Ei` 装着候选集合，`di` 装着长度的数码，`bi` 装着基。等式 `qd` 与 `qb` 说明这两个槽位确实由 `m` 的数码与 `B` 填充，而 `hE` 说明 `γ` 满足以 `Ei` 为集合槽位的描述。在这些数据之下，`Ei` 处的集合与 `envSet B m` 被证明具有相同的成员。
<!--ja-->
モジュールは、この問いの一つの実例のデータを集める。`B` は基礎集合、`γ` は長さ `k` の環境で、三つのスロットに名前が付く。`Ei` が候補の集合を、`di` が長さの数項を、`bi` が基礎を収める。等式 `qd` と `qb` は、この二つのスロットが `m` の数項と `B` で埋められていることを述べ、`hE` は、`γ` が集合スロットを `Ei` に置いた記述を満たすことを述べる。このデータのもとで、`Ei` の指す集合と `envSet B m` が同じ要素をもつことが示される。
<!--/-->

```agda

  into : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
       → ⟨ fst z ∈ fst (envSet B m) ⟩
```

<!--en-->
The first direction reads the slot set inward: any member of the set named at `Ei` is a member of the constructed `envSet B m`.
<!--zh-->
第一个方向把槽位集合向内读：`Ei` 处所指名集合的任何成员，都是已构造的 `envSet B m` 的成员。
<!--ja-->
最初の方向は、スロットの集合を内側へ読むものである。`Ei` の指す集合のどんな要素も、構成済みの `envSet B m` の要素である。
<!--/-->

```agda
  into z hz = subst (λ w → ⟨ w ∈ fst (envSet B m) ⟩)
    (sym (Recover.recovers B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov))
    (envSet-in B (Recover.g B m (z ∷ γ) zero (suc di) (suc bi) qd qb ov))
```

<!--en-->
The proof reuses the recovery of the previous chapter, pointed at the member itself. The hypothesis says that `z` belongs to the set at `Ei`, so the description applies at `z`: the recovery reads off `z` an environment `g` whose canonical graph is, as a set, `z` itself. The constructed set contains the canonical graph of every such environment, and transporting along that identification puts the member `z` into `envSet B m`.
<!--zh-->
证明复用上一章的恢复过程，并把它对准这个成员本身。前提说 `z` 属于 `Ei` 处的集合，于是描述在 `z` 处适用：恢复过程从 `z` 读出一个环境 `g`，其典范图作为集合正是 `z` 自己。已构造的集合包含每个这样的环境的典范图，沿这条等同传输后，成员 `z` 便落入 `envSet B m`。
<!--ja-->
証明は、前の章の復元をこの要素そのものに向けて再利用する。仮定は `z` が `Ei` の指す集合に属することを言うので、記述は `z` で適用できる。復元は `z` から環境 `g` を読み取り、その正準なグラフが集合として `z` 自身であると同定する。構成済みの集合はそのような環境の正準なグラフをすべて含むので、この同定に沿って輸送すれば、要素 `z` は `envSet B m` の中に入る。
<!--/-->

```agda
    where
    ov : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    ov = extAt-out Ei (envOverAt zero (suc di) (suc bi)) γ hE z hz
```

<!--en-->
The recovery needs the four clauses to hold at `z`, and the description supplies exactly that: applied at the member `z`, it yields the environment clause over the environment extended by `z`, with the length and base slots shifted past the new entry.
<!--zh-->
恢复需要那四条子句在 `z` 处成立，而描述给出的恰是这件事：把它施用于成员 `z`，便得到在扩展了 `z` 的环境上的环境子句，长度与基的槽位则越过新条目相应后移。
<!--ja-->
復元には、四つの節が `z` で成り立つことが要る。記述が与えるのはまさにこれである。要素 `z` に適用すれば、`z` で拡張した環境の上の環境の節が得られ、長さと基礎のスロットは新しい項目のぶんだけ後ろへずれる。
<!--/-->

```agda

  outof : (z : S) → ⟨ fst z ∈ fst (envSet B m) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
```

<!--en-->
The second direction reads outward: any member of the constructed `envSet B m` is a member of the set named at `Ei`.
<!--zh-->
第二个方向向外读：已构造的 `envSet B m` 的任何成员，都是 `Ei` 处所指名集合的成员。
<!--ja-->
第二の方向は外向きに読むものである。構成済みの `envSet B m` のどんな要素も、`Ei` の指す集合の要素である。
<!--/-->

```agda
  outof z hz = rec₁ (snd (fst z ∈ fst (lookup Ei γ)))
    (λ { (g , eg) →
```

<!--en-->
Membership in the constructed set hands over a truncated witness: an environment `g` whose canonical graph is `z`. The goal, being a membership statement, is a proposition, so the truncation may be consumed, and the membership characterization of the previous chapter is what produces the witness.
<!--zh-->
已构造集合中的隶属交出一个截断的见证：一个环境 `g`，其典范图就是 `z`。目标是隶属陈述，因而是命题，截断因此可以消耗；而产出见证的，正是上一章的隶属刻画。
<!--ja-->
構成済みの集合への所属は、切り詰められた証人を手渡す。それは環境 `g` であり、その正準なグラフが `z` である。目標は所属の主張、つまり命題なので、切り詰めは消去でき、証人を生み出すのは前の章の所属の特徴づけである。
<!--/-->

```agda
      extAt-in Ei (envOverAt zero (suc di) (suc bi)) γ hE z
        (envOverAt-transport (B ∷ nn m ∷ envS B g ∷ []) (z ∷ γ)
          (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
          (sym eg) (sym qd) (sym qb)
          (envOver B g)) })
```

<!--en-->
The recovered environment satisfies the environment clause at its own canonical environment, where the three slots hold `B`, the numeral of `m`, and its graph. The transport lemma moves that satisfaction to the extended environment `(z ∷ γ)` along the three equations, reading the canonical graph as `z`, the numeral as the entry at `di`, and `B` as the entry at `bi`. The description then applies, through its inward implication, to conclude that `z` belongs to the set at `Ei`.
<!--zh-->
恢复出的环境在它自己的典范环境处满足环境子句，那里三个槽位装着 `B`、`m` 的数码与它的图。搬运引理沿三条等式把这个满足搬到扩展环境 `(z ∷ γ)`：把典范图读作 `z`，把数码读作 `di` 处的条目，把 `B` 读作 `bi` 处的条目。描述随即经其内向蕴含适用，结论是 `z` 属于 `Ei` 处的集合。
<!--ja-->
復元された環境は、みずからの正準な環境、すなわち三つのスロットに `B` と `m` の数項とそのグラフが収まった環境で、環境の節を満たす。輸送の補題は、三つの等式に沿ってこの充足を拡張された環境 `(z ∷ γ)` へ運ぶ。正準なグラフを `z` と読み、数項を `di` の項目と読み、`B` を `bi` の項目と読むのである。記述はその内向きの含意を通して直ちに適用でき、`z` が `Ei` の指す集合に属すると結論される。
<!--/-->

```agda
    (envSet-out B m z hz)
```
</div>
</details>


<!--en-->
The environment handed to the transport comes from the membership characterization of the constructed set, applied at the member `z` with which this direction began.
<!--zh-->
交给搬运的那个环境来自已构造集合的隶属刻画，施用于本方向出发时的那个成员 `z`。
<!--ja-->
輸送に渡される環境は、構成済みの集合の所属の特徴づけから来る。この方向の出発点であった要素 `z` に適用されるのである。
<!--/-->

<!--en-->
## The constructed set satisfies the description

The second module turns the agreement around and asks the producing question: does the constructed environment set itself satisfy the description? Placed at the set slot, with the numeral of `m` and the base at the other two slots, it does, and this is what a clause that binds its own base and length needs when it fills those slots with the constructed data. The proof runs the same two moves as before, now in the order the description demands: every member of the constructed set is shown to satisfy the per-member clause, and every set satisfying that clause is shown to be a member.
<!--zh-->
## 已构造的集合满足描述

第二个模块把一致反过来，问的是产出方向：已构造的环境集自身满足这条描述吗？把它放在集合槽位、在另两个槽位放上 `m` 的数码与基之后，答案是肯定的；而这正是绑定自己的基与长度的子句在用已构造数据填充槽位时所需要的。证明沿与先前相同的两步运行，只是次序改由描述支配：已构造集合的每个成员都被证明满足逐成员子句，而每个满足该子句的集合也被证明是其成员。
<!--ja-->
## 構成した集合が記述を満たすこと

第二のモジュールは一致を逆向きに回し、生み出す方向を問う。構成済みの環境の集合それ自体は、この記述を満たすのであろうか。集合のスロットに置き、他の二つのスロットに `m` の数項と基礎を置けば、答えは肯定的である。これこそ、自分の基礎と長さを束縛する節が、構成済みのデータでスロットを埋める際に必要とするものである。証明は以前と同じ二つの働きを、今度は記述の要求する順序で行う。構成済みの集合の各要素が要素ごとの節を満たすこと、そしてその節を満たす集合がすべて要素であることが示される。
<!--/-->

<!--en-->
The module assumes no satisfaction hypothesis. Its three equations say that the set slot holds the constructed set itself, the length slot holds the numeral of `m`, and the base slot holds `B`; from these alone the full description at `γ` is proved.
<!--zh-->
模块不假设任何满足前提。它的三条等式说明：集合槽位装着已构造的集合自身，长度槽位装着 `m` 的数码，基槽位装着 `B`；仅凭这些，即可证明 `γ` 处的完整描述。
<!--ja-->
モジュールは充足に関する前提を一切仮定しない。三つの等式が、集合のスロットに構成済みの集合そのものが、長さのスロットに `m` の数項が、基礎のスロットに `B` が収まっていることを述べる。これだけから、`γ` での記述の全体が証明される。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module AmbientHolds (B : S) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k) (m : ℕ)
  (qE : fst (lookup Ei γ) ≡ fst (envSet B m))
  (qd : fst (lookup di γ) ≡ # m) (qb : fst (lookup bi γ) ≡ fst B)
  where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
The three equations are the whole hypothesis. Naming the set slot with the constructed set, the length slot with the numeral, and the base slot with the base is exactly what a clause does when it fills the three slots with constructed data, so the module proves the description in precisely the form such a clause consumes.
<!--zh-->
三条等式就是全部前提。用已构造集合点名集合槽位、用数码点名长度槽位、用基点名基槽位，恰是子句以已构造数据填充三个槽位时所做的事，因此模块证明的描述，正是这类子句所消费的形式。
<!--ja-->
三つの等式が前提のすべてである。集合のスロットを構成済みの集合で、長さのスロットを数項で、基礎のスロットを基礎で名指すのは、節が三つのスロットを構成済みのデータで埋めるときに行うことそのものであり、したがってモジュールが証明する記述は、そのような節が消費する形そのものである。
<!--/-->

```agda

  holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
  holds = extAt-in-both Ei (envOverAt zero (suc di) (suc bi)) γ fwd bwd
```

<!--en-->
The description is an extensional one: it says that the set at `Ei` contains exactly the environments, and its two universally quantified implications are proved separately and joined. This is the shape announced at the module head, now filled in.
<!--zh-->
这条描述是外延式的：它说 `Ei` 处的集合恰好包含那些环境；其两个全称蕴含分别证明后再合并。这正是模块开头预告的形状，此处将它填实。
<!--ja-->
記述は外延的なものである。`Ei` の指す集合がちょうどそれらの環境を含むことを述べ、その二つの全称含意を別々に証明してから結ぶ。モジュールの冒頭で予告した形が、ここで埋められる。
<!--/-->

```agda
    where
    fwd : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
```

<!--en-->
The forward implication is the producing direction: every member of the constructed set satisfies the per-member clause over the extended environment.
<!--zh-->
向前蕴含是产出方向：已构造集合的每个成员都在扩展环境上满足逐成员子句。
<!--ja-->
順方向の含意が生み出す方向である。構成済みの集合の各要素は、拡張された環境の上で要素ごとの節を満たす。
<!--/-->

```agda
    fwd z hz = rec₁ (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
      (λ { (g , eg) → envOverAt-transport (B ∷ nn m ∷ envS B g ∷ []) (z ∷ γ)
```

<!--en-->
The membership `hz` is first re-pointed at the constructed set along the equation `qE`, and the membership lemma of the previous chapter then hands over a truncated environment. The goal on the other side is a proposition, being one clause of a satisfaction judgment, so the truncated witness can be taken apart.
<!--zh-->
隶属 `hz` 先沿等式 `qE` 被重新指到已构造的集合上，上一章的隶属引理随即交出一个截断的环境。另一侧的目标是满足判断的一条子句，因而是命题，截断的见证因此可以拆开。
<!--ja-->
所属 `hz` は、まず等式 `qE` に沿って構成済みの集合へと指し直され、前の章の所属の補題が切り詰められた環境を手渡す。反対側の目標は充足の判断の一つの節、つまり命題なので、切り詰められた証人を分解できる。
<!--/-->

```agda
             (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
             (sym eg) (sym qd) (sym qb) (envOver B g) })
```

<!--en-->
The environment clause of the recovered environment is transported, exactly as in the reading direction, from its canonical environment to the extended environment of the judgment: the graph is read as the member `z`, the numeral as the entry at `di`, the base as the entry at `bi`. What remains is the clause itself, which is what the forward implication owes.
<!--zh-->
恢复出的环境的环境子句被搬运，方式与读取方向完全相同：从其典范环境搬到判断的扩展环境上，图被读作成员 `z`，数码被读作 `di` 处的条目，基被读作 `bi` 处的条目。余下的就是那条子句本身，这正是向前蕴含所欠的东西。
<!--ja-->
復元された環境の環境の節は、読み取りの方向とまったく同じやり方で輸送される。その正準な環境から判断の拡張された環境へ、グラフは要素 `z` と読み、数項は `di` の項目と読み、基礎は `bi` の項目と読まれる。残るのは節そのものであり、順方向の含意が負っているのはこれである。
<!--/-->

```agda
      (envSet-out B m z (subst (λ w → ⟨ fst z ∈ w ⟩) qE hz))
```

<!--en-->
The environment handed to the transport comes from the membership characterization of the constructed set, with `qE` supplying the first step that reads the member as a member of `envSet B m`.
<!--zh-->
交给搬运的那个环境来自已构造集合的隶属刻画，而 `qE` 供给了第一步：把该成员读作 `envSet B m` 的成员。
<!--ja-->
輸送に渡される環境は、構成済みの集合の所属の特徴付けから来る。`qE` が最初の一歩、すなわちその要素を `envSet B m` の要素として読み直す段階を供給する。
<!--/-->

```agda

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
```

<!--en-->
The backward implication is the reading direction: whatever satisfies the per-member clause over the extended environment belongs to the set at `Ei`.
<!--zh-->
向后蕴含是读取方向：凡在扩展环境上满足逐成员子句者，都属于 `Ei` 处的集合。
<!--ja-->
逆方向の含意は読み取りの方向である。拡張された環境の上で要素ごとの節を満たすものは、すべて `Ei` の指す集合に属する。
<!--/-->

```agda
    bwd z h = subst (λ w → ⟨ fst z ∈ w ⟩) (sym qE)
      (subst (λ w → ⟨ w ∈ fst (envSet B m) ⟩)
        (sym (Recover.recovers B m (z ∷ γ) zero (suc di) (suc bi) qd qb h))
        (envSet-in B (Recover.g B m (z ∷ γ) zero (suc di) (suc bi) qd qb h)))
```
</div>
</details>


<!--en-->
The clause at `z` is the recovery's input: the recovered environment's canonical graph agrees with `z` as a set, and the constructed set contains that graph. The first transport reads the recovered graph as `z`, so the membership lands in `envSet B m`; the second runs backward along `qE` and turns membership in `envSet B m` into membership in the set at `Ei`.
<!--zh-->
`z` 处的子句正是恢复的输入：恢复出的环境的典范图作为集合与 `z` 一致，而已构造的集合包含那个图。第一次传输把恢复出的图读作 `z`，使隶属落入 `envSet B m`；第二次沿 `qE` 反向进行，把对 `envSet B m` 的隶属变为对 `Ei` 处集合的隶属。
<!--ja-->
`z` での節は、復元の入力である。復元された環境の正準なグラフは集合として `z` と一致し、構成済みの集合はそのグラフを含む。最初の輸送が復元されたグラフを `z` と読み、所属を `envSet B m` の中に着地させ、二度目の輸送が `qE` に沿って逆に走り、`envSet B m` への所属を `Ei` の指す集合への所属へ変える。
<!--/-->