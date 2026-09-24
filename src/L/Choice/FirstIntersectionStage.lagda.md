```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The first stage meeting a set
<!--zh-->
# 首次与集合相交的层
<!--ja-->
# 集合と交わる最初の段階
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
This chapter provides two ingredients of the internal choice construction. The
first is a lemma about least stages. When a property of ordinals holds for the
first time, it holds at a least stage; whether that stage is a successor is not
automatic, for the property may hold first at the zero ordinal. The chapter
proves the conditional form that the argument needs: if, besides the least
stage, a carve merely exists, an ordinal below it at whose successor the
property already holds, then the least stage is a successor with a unique
predecessor. The second ingredient is a bounding ordinal: for a constructible
set, one ordinal whose stage contains the set, its members, the members of its
members, and the limit level of the tower.

The material serves a comparison that proceeds by two keys. Two sets that first
appear at different stages are compared by their birth ordinals and by nothing
else; only sets that first appear at the same stage are compared by their names
within that stage. The first ingredient makes each birth ordinal a definite
object rather than a mere existence, and the second guarantees that the
material of a whole family of candidates lives inside one stage, so that the
name comparison has a common arena.
<!--zh-->
本章为内部选择构造提供两样原料。第一是关于最小层的引理。当一条序数性质首次成立时，它在一个最小层处成立；该层是否为后继并非自动成立，因为性质可能在零序数处首次成立。本章证明论证所需的条件形式：若除最小层之外，一次雕出仅仅存在，即存在低于它的序数 `δ` 使性质在后继 `sucV δ` 处已经成立，则最小层是后继，且有唯一的前一层。第二样原料是一个上界序数：对可构造集合而言，存在一个序数，其层同时容纳该集合、它的成员、成员的成员，以及塔的极限层。

这些材料服务于一把双钥匙的比较。首次出现在不同层的两个集合，仅凭各自的诞生序数比较，别无其他；只有首次出现在同一层的集合，才在该层之内按名字比较。第一样原料使每个诞生序数成为确定的对象，而非单纯的存在；第二样原料保证一整族候选者所需的材料都住进同一个层，从而名字的比较有共同的场地。
<!--ja-->
本章は、内部の選択の構成のための二つの材料を提供する。第一は最小段階についての補題である。順序数の性質がはじめて成立するとき、それは最小の段階で成立する。その段階が後者であるかどうかは自動ではない。性質は零順序数ではじめて成立するかもしれないからである。本章は、議論に必要な条件付きの形を証明する。最小の段階のほかに、切り出しが単に存在するならば、すなわちその下の順序数 `δ` で、後者 `sucV δ` ですでに性質が成立しているならば、最小の段階は後者であり、一意な直前の段階をもつ。第二の材料は上界の順序数である。構成可能な集合に対し、その集合、その要素、その要素の要素、そして塔の極限段階を同時に含む一つの順序数がある。

この材料に仕えるのは、二つの鍵による比較である。異なる段階ではじめて現れた二つの集合は、誕生の順序数だけによって比較され、それ以外の何ものによっても比較されない。同じ段階ではじめて現れた集合どうしだけが、その段階の中の名前によって比較される。第一の材料は、それぞれの誕生の順序数を、単なる存在ではなく確定した対象にする。第二の材料は、候補の族全体が必要とする材料が一つの段階の中に住むことを保証し、名前の比較に共通の場を与える。
<!--/-->

```agda
module L.Choice.FirstIntersectionStage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd; isL; Lset; Lset-layer; Lset-out
        ; Lset-mono; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; bound2; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem
  using ( isLeastOrd; stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
```

<!--en-->
The chapter runs under one hypothesis, an excluded-middle instance at the
successor of the model's level, and every statement below is made inside that
setting.
<!--zh-->
全章在唯一一条假设下运行：模型层级的后继处的一份排中律实例；以下每条陈述都在这一设定之内作出。
<!--ja-->
本章は一つの仮定のもとで進む。モデルのレベルの後続での排中律の実例であり、以下の主張はすべてその設定の中でなされる。
<!--/-->

<!--en-->
The question of the chapter is one about first appearances. A constructible set
enters the tower of stages at some point; the ambient hierarchy, in which the
tower lives, has irreflexive membership, so no ordinal contains itself, and its
successors are understood: an ordinal sits inside its own successor, and a
member of a successor is a member of the ordinal or the ordinal itself.
<!--zh-->
本章的问题是关于首次出现的。一个可构造集合会在某个时刻进入层之塔；塔所居于的环境层级具有非自反的隶属，故没有序数包含自身，而其后继的性质也已清楚：序数坐在自己的后继之内，后继的成员或是该序数的成员、或是该序数本身。
<!--ja-->
本章の問いは、はじめての出現についてのものである。構成可能な集合は、いつか塔に入る。塔の住む周囲の階層は反射しない所属をもち、だからどの順序数も自分自身を含まず、後者の性質も分かっている。順序数は自分の後者の中に坐り、後者の要素はその順序数の要素か、その順序数自身のどちらかである。
<!--/-->

<!--en-->
The constructible side answers with its tower `Lset`{.Agda}, indexed by
ordinals, which are sets of the hierarchy, never by universe levels of the
host. Ordinality `IsOrd`{.Agda} is itself a proposition; the tower has a layer
relation, an outward decomposition, and monotonicity; and transitivity moves
members across layers.
<!--zh-->
可构造一侧以塔 `Lset`{.Agda} 作答，塔由序数索引，序数是层级的集合，而非宿主的宇宙层级。序数性 `IsOrd`{.Agda} 本身是命题；塔有层关系、向外的分解与单调性；传递性则在层之间搬运成员。
<!--ja-->
構成可能の側は、塔 `Lset`{.Agda} で答える。塔は順序数で添字づけられ、順序数は階層の集合であり、ホストの宇宙レベルではない。順序数性 `IsOrd`{.Agda} はそれ自体命題であり、塔には層の関係、外向きの分解、単調性があり、推移性が層の間で要素を運ぶ。
<!--/-->

<!--en-->
The argument turns on comparisons and on stages. Comparing an ordinal below a
stage with the stage itself is what decides whether the stage overshoots a
successor, and members of ordinals and successors of ordinals are again
ordinals. Each constructible set carries its earliest ordinal, delivered with
ordinality and membership, and minimality stated refutationally. Two ordinals
have a common bound. And the successor identity says the next stage is exactly
the definable subsets of the previous one, which is the step by which anything
enters the tower at all.
<!--zh-->
论证依靠比较与层。把低于某层的序数与该层自身相比，正是判定该层是否越过一个后继的方法；序数的成员与序数的后继都仍是序数。每个可构造集合携带着它最早的序数，连同序数性与隶属交付，而极小性以反驳形式陈述。两个序数有共同上界。后继恒等式则说：下一层恰是上一层的可定义子集，这正是任何东西得以进入塔的那一步。
<!--ja-->
議論を支えるのは、比較と段階である。段階の下の順序数を段階そのものと比べることが、その段階がある後者を行き過ぎていないかの判定である。順序数の要素も後者もまた順序数である。各構成可能集合はその最初の順序数を携え、順序数性と所属とともに渡され、極小性は反駁として述べられる。二つの順序数には共通の上界がある。そして後者の恒等式は、次の段階がちょうど前の段階の定義可能な部分集合であると言う。何ものかが塔に入るのは、まさにこの一歩によってである。
<!--/-->

<!--en-->
The argument is written in three propositional moves: a split into cases, a
refutation ending in the empty type, and an existence known only to be
existence.
<!--zh-->
论证以三个命题动作写成：分裂成情形、以空类型告终的反驳，以及仅知其为存在的存在。
<!--ja-->
議論は三つの命題の動きで書かれる。場合への分裂、空型で終わる反駁、そして存在することがだけ分かっている存在である。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
```

<!--en-->
A predecessor pairs an ordinal with propositional evidence. Such pairs are determined by their first component, and the cumulative hierarchy itself is a set, so equality of predecessors reduces to equality of the underlying ordinals.
<!--zh-->
前一层把一个序数与命题性的证据配成一对。这类序对由第一分量决定；累积层级本身又是集合，因此前一层的相等归结为其序数分量的相等。
<!--ja-->
直前の段階は、順序数と命題的な証拠との対である。この種の対は第一成分で決まり、累積階層自身も集合なので、直前の段階の等しさは順序数成分の等しさに帰着する。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )
```

<!--en-->
The hierarchy's infinity construction supplies both the von Neumann successor `sucV`{.Agda} and the limit level `ω`{.Agda} used in the bound.
<!--zh-->
层级的无穷构造同时给出冯·诺伊曼后继 `sucV`{.Agda}，以及上界所要包含的极限层 `ω`{.Agda}。
<!--ja-->
階層の無限の構成は、フォン・ノイマンの後者 `sucV`{.Agda} と、上界に含める極限段階 `ω`{.Agda} の両方を与える。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
```

<!--en-->
Structure membership `∈ˢ` is the relation in which ordinality, stages and
minimality are all stated.
<!--zh-->
结构隶属 `∈ˢ` 是序数性、层与极小性共同陈述其中的关系。
<!--ja-->
構造の所属 `∈ˢ` は、順序数性も段階も極小性もその中で述べられる関係である。
<!--/-->

<!--en-->
## The predecessor of a least stage
<!--zh-->
## 最小层的前一层
<!--ja-->
## 最小段階の直前の段階
<!--/-->

<!--en-->
The question is whether the least stage at which something appears is a
successor, and which stage it succeeds. A least stage taken alone need not be
one, for the property may begin at zero; what the construction produces, under
the additional hypothesis of a carve below, is the unique predecessor.
<!--zh-->
问题是：某物现身的那个最小层是否为后继，若是，它后继的是哪一层。单独的最小层未必是后继，因为性质可能从零开始；构造在「其下有雕出」这一附加假设之下产出唯一的前一层。
<!--ja-->
問いは、何かが現れる最小の段階が後者であるか、そしてどの段階を後者とするかである。最小の段階だけでは後者とは限らない。性質は零からはじまるかもしれないからである。構成が産出するのは、「下に切り出しがある」という追加の仮定のもとでの、一意な直前の段階である。
<!--/-->

<!--en-->
A successor determines what it succeeds, at least among ordinals. Compare a
candidate predecessor with another: each belongs to the successor of the other,
so each is a member of the other or equal to it, and two ordinals cannot be
members of each other, since transitivity would then make one a member of
itself. So being the predecessor of a given ordinal is a proposition, which is
what lets a merely-existing predecessor be read as a definite one.

That a least stage has a predecessor at all takes two inputs, and it is worth
seeing them separately. The first is the least stage itself: an ordinal `σ` at
which the property holds, with minimality stated refutationally, that no
smaller ordinal has it. The second is the mere existence of a carve at `σ`: some
ordinal `δ` below `σ` at whose successor the property already holds. Given a
carve, minimality rules out the successor staying strictly below, and the
no-overshoot comparison leaves one case: the successor of the carved ordinal is
exactly `σ`. So the least stage is a successor, and the carved ordinal is its
predecessor. Without the carve nothing follows: the property may hold first at
the zero ordinal, below which no ordinal exists at all.
<!--zh-->
后继决定它所后继的东西，至少在序数之内如此。把一个候选前一层与另一个相比：各自属于对方的后继，故各自或是对方的成员、或与对方相等；而两个序数不能互为成员，否则传递性会使其一属于自身。于是「是给定序数的前一层」是命题，正是这一点使一个仅仅存在的前一层可以被读作一个确定的前一层。

最小层凭什么有前一层？这需要两样输入，值得分开看。第一是最小层自身：性质在其中成立的序数 `σ`，其极小性以反驳形式陈述，即没有更小的序数拥有该性质。第二是 `σ` 处雕出的仅仅存在：`σ` 以下的某个序数 `δ`，其后续 `sucV δ` 处性质已经成立。有了雕出，极小性排除「后继仍严格在下」，而不越头的比较只剩一种情形：被雕出序数的后继恰是 `σ`。于是最小层是后继，而被雕出的序数就是它的前一层。没有雕出则推不出任何东西：性质可能恰在零序数处首次成立，而零以下根本没有序数。
<!--ja-->
後者は、それが後者とするものを決める。少なくとも順序数の間ではそうである。候補の直前の段階を別のものと比べると、それぞれが相手の後者に属するので、それぞれは相手の要素か等しいかのどちらかであり、二つの順序数が互いに要素であることはあり得ない。推移性から一方が自分自身の要素になるからである。そこで、与えられた順序数の直前の段階であることは命題になり、これこそが、単に存在するだけの直前の段階を確定したものとして読める理由である。

最小の段階が直前の段階をもつには、二つの入力が要る。分けて見る価値がある。第一は最小の段階そのものである。性質が成立する順序数 `σ` であり、極小性は反駁として述べられる。より小さい順序数は性質をもたない、と。第二は `σ` での切り出しの単なる存在である。`σ` の下の順序数 `δ` で、その後者 `sucV δ` ですでに性質が成立しているもの。切り出しがあれば、極小性が「後者が厳密に下にとどまる」ことを排除し、行き過ぎない比較は一つの場合を残す。切り出された順序数の後者はちょうど `σ` である、と。ゆえに最小の段階は後者であり、切り出された順序数がその直前の段階である。切り出しなしには何も従わない。性質は零順序数ではじめて成立するかもしれず、零の下には順序数がそもそも存在しないからである。
<!--/-->

```agda
IsPredOf : S → S → Type (ℓ-suc ℓ)
IsPredOf σ δ = IsOrd δ × (sucV δ ≡ σ)
```

<!--en-->
A candidate predecessor `δ` of an ordinal `σ` is an ordinal whose von Neumann
successor is `σ` itself. Both halves matter: ordinality is what the comparison
needs, and the equation is what pins `δ` to `σ`.
<!--zh-->
序数 `σ` 的候选前一层 `δ` 是一个序数，其冯·诺伊曼后继就是 `σ` 本身。两半都不可或缺：序数性是比较所需的，等式则是把 `δ` 钉在 `σ` 上的。
<!--ja-->
順序数 `σ` の候補の直前の段階 `δ` とは、そのフォン・ノイマンの後者が `σ` 自身であるような順序数である。両方の半分が要る。順序数性は比較が使うものであり、等式は `δ` を `σ` に釘づけするものである。
<!--/-->

```agda
private
  cycle₂ : (a b : S) → IsOrd a → ⟨ a ∈ˢ b ⟩ → ⟨ b ∈ˢ a ⟩ → ⊥₀
  cycle₂ a b orda a∈b b∈a = ∈-irrefl a (orda .fst a∈b b∈a)
```

<!--en-->
No ordinal can be a member of one of its own members: transitivity would carry
the membership around the two-step cycle back to `a` itself, contradicting
irreflexivity. This two-step impossibility forbids two ordinals from
containing each other.
<!--zh-->
没有序数能属于它自己的某个成员：传递性会把这条隶属沿两步循环搬回 `a` 自身，与非自反性矛盾。正是这个两步的不可能性，禁止两个序数互为成员。
<!--ja-->
どの順序数も、自分の要素である順序数の要素にはなれない。推移性がこの所属を二歩の循環で `a` 自身へ運び、非反射性と衝突するからである。この二歩の不可能性こそ、二つの順序数が互いを含むことを禁じるものである。
<!--/-->

```agda
  mem-branch : (δ δ' : S) → IsOrd δ → ⟨ δ' ∈ˢ sucV δ ⟩ → ⟨ δ ∈ˢ δ' ⟩ → δ ≡ δ'
  mem-branch δ δ' ordδ δ'∈sδ δ∈δ' =
    ∈sucV-elim {A = δ} {x = δ'} (setIsSet δ δ') δ'∈sδ
      (λ δ'∈δ → ⊥₀-rec (cycle₂ δ δ' ordδ δ∈δ' δ'∈δ))
      (λ δ'≡δ → sym δ'≡δ)
```

<!--en-->
The membership branch reads: `δ'` is a member of the successor of `δ`, and `δ`
is a member of `δ'`; the conclusion must be `δ ≡ δ'`. If `δ'` were a member of
`δ` itself, the two-step cycle would close; so `δ'` is `δ` itself, and the
elimination returns exactly that.
<!--zh-->
隶属分支读作：`δ'` 属于 `δ` 的后继，且 `δ` 属于 `δ'`；结论必为 `δ ≡ δ'`。倘若 `δ'` 属于 `δ` 自身，两步循环便会闭合；故 `δ'` 就是 `δ` 自身，消去恰返回这一点。
<!--ja-->
所属の分岐はこう読む。`δ'` は `δ` の後者の要素であり、かつ `δ` は `δ'` の要素である。結論は `δ ≡ δ'` でなければならない。もし `δ'` が `δ` 自身の要素なら、二歩の循環が閉じてしまう。だから `δ'` は `δ` 自身であり、消去はまさにそれを返す。
<!--/-->

```agda
ord-suc-inj : (δ δ' : S) → IsOrd δ → sucV δ ≡ sucV δ' → δ ≡ δ'
ord-suc-inj δ δ' ordδ e =
  ∈sucV-elim {A = δ'} {x = δ} (setIsSet δ δ') δ∈sδ'
    (mem-branch δ δ' ordδ δ'∈sδ)
    (λ δ≡δ' → δ≡δ')
```

<!--en-->
The successor operation is injective on ordinals. From the equation of
successors, `δ` is a member of `sucV δ'`; the elimination offers two readings.
Either `δ` is a member of `δ'`, in which case the membership branch closes the
cycle and gives the equality, or `δ` already is `δ'`. A successor determines
what it succeeds.
<!--zh-->
后继运算在序数上是单射的。由后继的等式，`δ` 属于 `sucV δ'`；消去给出两种读法。要么 `δ` 属于 `δ'`，此时隶属分支闭合循环并给出等式；要么 `δ` 本来就是 `δ'`。后继决定它所后继者。
<!--ja-->
後者の演算は順序数の上で単射である。後者の等式から、`δ` は `sucV δ'` の要素である。消去は二つの読みを示す。`δ` が `δ'` の要素なら、所属の分岐が循環を閉じて等式を与え、さもなくば `δ` ははじめから `δ'` である。後者は、それの後者とするものを決める。
<!--/-->

```agda
  where
  δ∈sδ' : ⟨ δ ∈ˢ sucV δ' ⟩
  δ∈sδ' = subst (λ w → ⟨ δ ∈ˢ w ⟩) e (self∈sucV δ)
  δ'∈sδ : ⟨ δ' ∈ˢ sucV δ ⟩
  δ'∈sδ = subst (λ w → ⟨ δ' ∈ˢ w ⟩) (sym e) (self∈sucV δ')
```

<!--en-->
The two memberships feeding the elimination come from the standing fact that an
ordinal sits inside its own successor, transported along the equation and its
reverse.
<!--zh-->
喂给消去的两条隶属来自既有事实「序数坐在自己的后继之内」，沿等式及其反向运输而得。
<!--ja-->
消去に渡す二つの所属は、順序数が自分の後者の中に坐るという既存の事実から、等式とその逆向きに沿って輸送したものである。
<!--/-->

```agda
isPropPredOf : (σ : S) → isProp (Σ[ δ ∈ S ] IsPredOf σ δ)
isPropPredOf σ (δ , (ordδ , e)) (δ' , (ordδ' , e')) =
  Σ≡Prop (λ d → isProp× (isPropIsOrd d) (setIsSet (sucV d) σ))
    (ord-suc-inj δ δ' ordδ (e ∙ sym e'))
```

<!--en-->
Any two predecessors of one ordinal are therefore equal. The first components
agree by injectivity, and the remaining data are propositions, so the whole
type of predecessors is a proposition. This is what makes a merely-existing
predecessor usable as a definite one: unwrapping a truncation into a
proposition-valued target is always legitimate.
<!--zh-->
于是同一序数的任意两个前一层相等。第一分量由单射性一致，其余数据都是命题，故前一层组成的整个类型是命题。正是这一点使「仅仅存在的前一层」可当作确定的前一层使用：把截断展开到命题值的目标永远合法。
<!--ja-->
したがって、同じ順序数のどの二つの直前の段階も等しくなる。第一成分は単射性により一致し、残りのデータは命題なので、直前の段階の型全体が命題になる。これこそ、単に存在するだけの直前の段階を確定したものとして使える理由である。切り詰めを命題値の対象へほどくのは、つねに正当である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ (P : S → hProp (ℓ-suc ℓ)) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The least-stage argument is now run once for every property of ordinals at
once: the property is a parameter, and nothing below ever reads into it.
<!--zh-->
最小层论证对每条序数性质同时只写一次：性质是参数，以下任何地方都不读入其内部。
<!--ja-->
最小段階の議論は、順序数の性質ごとに一度だけ書かれる。性質はパラメータであり、以下のどこでもその内側を読むことはない。
<!--/-->

```agda
  Carved : S → Type (ℓ-suc ℓ)
  Carved σ = Σ[ δ ∈ S ] (⟨ δ ∈ˢ σ ⟩ × ⟨ P (sucV δ) ⟩)
```

<!--en-->
A carve at `σ` is the datum the argument runs on: an ordinal `δ` strictly below
`σ` whose successor already carries the property. If a carve merely exists, the
least stage cannot be far above `δ`, for the property already holds at
`sucV δ`.
<!--zh-->
`σ` 处的一次雕出是论证所运行的数据：一个严格低于 `σ` 的序数 `δ`，其后继已携带该性质。若雕出仅仅存在，最小层就不可能远在 `δ` 之上，因为性质在 `sucV δ` 处已经成立。
<!--ja-->
`σ` での切り出しとは、議論が動くデータである。`σ` より厳密に下の順序数 `δ` で、その後者がすでに性質を帯びているもの。切り出しが単に存在するだけでも、最小の段階が `δ` のはるか上にあることはあり得ない。性質はすでに `sucV δ` で成立しているからである。
<!--/-->

```agda
  private
    below-case : (σ δ : S) → isLeastOrd P σ → IsOrd δ → ⟨ P (sucV δ) ⟩
               → ⟨ sucV δ ∈ˢ σ ⟩ → sucV δ ≡ σ
    below-case σ δ least ordδ m s∈σ =
      ⊥₀-rec (least (sucV δ) (suc-ord ordδ) m s∈σ)
```

<!--en-->
The below branch handles the case in which the successor stays strictly below
the least stage. Minimality is stated refutationally, and the hypotheses of
this branch are exactly its premises, so `least` yields a contradiction first;
`⊥*-rec` then eliminates that contradiction to the path the branch owes,
`sucV δ ≡ σ`.
<!--zh-->
below 分支处理「后继仍严格低于最小层」的情形。极小性以反驳形式陈述，而本分支的假设恰是它的前提，故 `least` 先给出矛盾；`⊥*-rec` 再把该矛盾消去成分支所欠的路径 `sucV δ ≡ σ`。
<!--ja-->
下の分岐は、後者が最小の段階より厳密に下にとどまる場合を扱う。極小性は反駁として述べられており、この分岐の仮定はその前提そのものなので、`least` がまず矛盾を与える。`⊥*-rec` がその矛盾を、この分岐が負うパス `sucV δ ≡ σ` へ消去する。
<!--/-->

```agda
    same-case : (σ δ : S) → sucV δ ≡ σ → sucV δ ≡ σ
    same-case σ δ e = e
```

<!--en-->
The equal case needs no work at all: the identification of the successor with
the least stage is what the case was handed.
<!--zh-->
相等情形无须任何工作：交给该情形的恰是「后继与最小层等同」这件事本身。
<!--ja-->
等しい場合は何の仕事も要らない。この場合に渡されたのは、後者が最小の段階と等しいという同定そのものだからである。
<!--/-->

```agda
    atCarve : (σ : S) → IsOrd σ → isLeastOrd P σ
            → Carved σ → Σ[ δ ∈ S ] IsPredOf σ δ
    atCarve σ ordσ least (δ , (δ∈σ , m)) = δ , (ordδ , suc≡σ)
```

<!--en-->
`atCarve` turns a carve into a definite predecessor. The witness `δ` is kept,
its ordinality is recovered from belonging to the ordinal `σ`, and the equation
pinning `sucV δ` to `σ` is the content of the case analysis.
<!--zh-->
`atCarve` 把一次雕出变成确定的前一层。见证 `δ` 被保留，其序数性由属于序数 `σ` 而恢复，而把 `sucV δ` 钉到 `σ` 上的等式正是那场情形分析的内容。
<!--ja-->
`atCarve` は切り出しを確定した直前の段階に変える。証人 `δ` はそのまま残り、その順序数性は順序数 `σ` への所属から回復し、`sucV δ` を `σ` に釘づけする等式が場合分析の内容である。
<!--/-->

```agda
      where
      ordδ : IsOrd δ
      ordδ = mem-ord {A = σ} ordσ δ δ∈σ
```

<!--en-->
Ordinality of `δ` is inherited from the ordinal `σ`, members of ordinals
being ordinals.
<!--zh-->
`δ` 的序数性承继自序数 `σ`，因为序数的成员是序数。
<!--ja-->
`δ` の順序数性は順序数 `σ` から受け継がれる。順序数の要素は順序数だからである。
<!--/-->

```agda
      suc≡σ : sucV δ ≡ σ
      suc≡σ = ⊎-rec (below-case σ δ least ordδ m) (same-case σ δ)
        (suc∈or≡ δ σ ordδ ordσ δ∈σ)
```

<!--en-->
Given `δ ∈ σ`, `suc∈or≡` leaves exactly two possibilities for its successor: it remains strictly below `σ`, or it equals `σ`. Minimality refutes the first, so the second gives the required equation.
<!--zh-->
由 `δ ∈ σ` 出发，`suc∈or≡` 为其后继留下两种可能：仍严格低于 `σ`，或等于 `σ`。极小性排除前者，后者便给出所需等式。
<!--ja-->
`δ ∈ σ` のもとで、`suc∈or≡` はその後者に二つの可能性だけを残す。`σ` より厳密に下にとどまるか、`σ` と等しいかである。極小性が前者を退けるので、後者が必要な等式を与える。
<!--/-->

```agda
  predOf : (σ : S) → IsOrd σ → isLeastOrd P σ → ∥ Carved σ ∥₁
         → Σ[ δ ∈ S ] IsPredOf σ δ
  predOf σ ordσ least = rec₁ (isPropPredOf σ) (atCarve σ ordσ least)
```

<!--en-->
`predOf` consumes a carve known only to exist and returns the predecessor. The
truncated input is eliminated into the proposition that the predecessor type
is, so no choice among hypothetical carves is ever made; whichever carve the
truncation hands over, the answer is the same definite predecessor.
<!--zh-->
`predOf` 消费一个仅知其存在的雕出，返回前一层。截断的输入被消去到「前一层类型是命题」这一事实之中，因此从不在假想的雕出之间作选择；无论截断交出哪次雕出，答案都是同一个确定的前一层。
<!--ja-->
`predOf` は、存在することだけ分かっている切り出しを消費し、直前の段階を返す。切り詰められた入力は「直前の段階の型が命題である」という事実へ消去されるので、仮の切り出しの間で選択が行われることはない。切り詰めがどの切り出しを渡しても、答えは同じ確定した直前の段階である。
<!--/-->

```agda
  carveAt : (σ z : S) → ⟨ z ∈ˢ Lset σ ⟩
          → ((δ : S) → ⟨ z ∈ˢ Lset (sucV δ) ⟩ → ⟨ P (sucV δ) ⟩)
          → ∥ Carved σ ∥₁
```

<!--en-->
`carveAt` produces a carve from a member `z` of the least stage, together with
the observation that whenever `z` appears at a successor stage, the property
already holds there. That observation is exactly the shape of the descent into
the tower: appearing at a stage is appearing inside a definable powerset of an
earlier stage, and every definable powerset is a successor stage by the
successor identity.
<!--zh-->
`carveAt` 从最小层的一个成员 `z` 造出雕出，配合的是这样一条观察：但凡 `z` 在某个后继层现身，性质便已在彼处成立。这正是进入塔之下降的形状：出现在某层，就是出现在某个更早层的可定义幂集之内，而由后继恒等式，每个可定义幂集都是一个后继层。
<!--ja-->
`carveAt` は、最小の段階の要素 `z` から切り出しを作る。そこには、`z` がどこかの後者の段階で現れるなら、性質はすでにそこで成立するという観察が伴う。これは塔への下降の形そのものである。段階への出現とは、より前の段階の定義可能冪集合の内側への出現であり、後者の恒等式により、どの定義可能冪集合も後者の段階である。
<!--/-->

```agda
  carveAt σ z z∈Lσ k = map₁
    (λ { (δ , (δ∈σ , z∈𝒟)) → δ , (δ∈σ
      , k δ (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Lset-suc δ)) z∈𝒟)) })
    (Lset-out σ z z∈Lσ)
```
</div>
</details>

<!--en-->
The tower decomposes the membership of `z` truncatedly: some stage `δ` below
`σ` with `z` in the definable powerset of `Lset δ`. The decomposition is mapped
inside the truncation only: the successor identity, read backwards, transports
`z` from `𝒟ₒ (Lset δ)` into `Lset (sucV δ)`, the observation `k` fires at that
successor, and the resulting carve is injected back into the truncation.
<!--zh-->
塔以截断的方式分解 `z` 的隶属：给出某个低于 `σ` 的层 `δ`，使 `z` 落在 `Lset δ` 的可定义幂集之内。映射只在截断内部进行：后继恒等式反向读取，把 `z` 从 `𝒟ₒ (Lset δ)` 搬到 `Lset (sucV δ)`，观察 `k` 在该后继处触发，所得的雕出被重新注入截断。
<!--ja-->
塔は `z` の所属を切り詰めた形で分解する。`σ` の下のある段階 `δ` で、`z` が `Lset δ` の定義可能冪集合の中にある、というものである。写像は切り詰めの内側だけで行われる。後者の恒等式を逆向きに読んで、`z` を `𝒟ₒ (Lset δ)` から `Lset (sucV δ)` へ運び、観察 `k` がその後者で発火し、できた切り出しが切り詰めへ注入し戻される。
<!--/-->

<!--en-->
## One stage for everything below a set
<!--zh-->
## 一层装下一个集合以下的一切
<!--ja-->
## 集合の下方全体を収める一つの段階
<!--/-->

<!--en-->
This section turns stage transitivity and an ordinal bound into one level that
contains a set's members, their members, and the limit level `ω`.
<!--zh-->
本节用层的传递性与序数上界，得到一个同时包含集合的成员、成员的成员以及极限层 `ω` 的层。
<!--ja-->
この節では、段階の推移性と順序数の上界から、集合の要素、その要素の要素、そして極限段階 `ω` を同時に含む一つの層を得る。
<!--/-->

<!--en-->
The other thing the construction needs is a bound, and no comparison is involved
in getting one. A stage is transitive, so the stage of a set already holds the
set's members, and their members after them; the earliest stage is a stage like
any other, so it serves.

One more ordinal remains to be fixed: the tower's limit level. The comparison
ahead is written in the object language, and the codes of all parameter-free formulas
`Formula ⊥* n`{.Agda}, of every arity, belong to `Lset ω`{.Agda}; such a code may have free variables, so
these are formulas, not sentences. A full name of a member of a successor stage
says more than its code: it names the arity and a vector of parameters from
earlier stages. The bound covers the codes, because `ω ∈ β` and monotonicity
lift `Lset ω`{.Agda} into `Lset β`{.Agda}; the parameters lie below the bound
for the reason the next fact records: members of the set and members of those
land in the same level.
<!--zh-->
构造还需要另一样东西：一个上界，而取得它不牵涉任何比较。层传递，故一个集合的层已经装着该集合的诸成员，以及其后它们的诸成员；最早的层与别的层无异，故它就够用。

还需确定一个包含塔的极限层的序数。前方的比较以对象语言书写，而各元数的无常元公式 `Formula ⊥* n`{.Agda} 的码都属于 `Lset ω`{.Agda}；这样的码可以带有自由变量，因此它们是公式，而非句子。后继层中一个成员的完整名字所说的多于它的码：它还要指名元数，以及取自更早层的参数向量。这里造出的界覆盖码，因为 `ω ∈ β` 加上单调性把 `Lset ω`{.Agda} 抬进 `Lset β`{.Agda}；参数低于界则另有原因，下一条事实记录的正是它：集合的成员与成员的成员落在同一层中。
<!--ja-->
構成にはもう一つ、上界が要る。それを得るのに比較は関わらない。段階は推移的であり、集合の段階はすでにその要素を、その次にはその要素の要素を収めている。最初の段階も他の段階と同じ段階なので、それで足りる。

もう一つ確定すべき順序数は、塔の極限段階である。先の比較は対象言語で書かれ、各アリティの無定数の論理式 `Formula ⊥* n`{.Agda} の符号は、いずれも `Lset ω`{.Agda} に属する。そのような符号は自由変数をもち得るので、これらは文ではなく論理式である。後者の段階の要素の完全な名前は、符号より多くを語る。アリティと、より前の段階から取ったパラメータのベクトルも名指すのである。ここで作る界が覆うのは符号のほうで、`ω ∈ β` と単調性が `Lset ω`{.Agda} を `Lset β`{.Agda} へ持ち上げる。パラメータが界の下にあるのは別の理由によるもので、次の事実がまさにそれを記録する。集合の要素とその要素の要素が同じ層に落ちる、と。
<!--/-->

```agda
stage-below : (a : S) (p : ⟨ isL a ⟩) (x : S) → ⟨ x ∈ˢ a ⟩
            → ⟨ x ∈ˢ Lset (stage a p) ⟩
stage-below a p x x∈a =
  layer-trans (Lset-layer (stage a p)) x∈a (stage-mem a p)
```

<!--en-->
Stages are transitive, and the earliest stage of `a` is a stage. So a member
`x` of `a` lies in the tower's level at `a`'s own stage: transitivity moves the
membership from the set into the level that holds the set.
<!--zh-->
层传递，而 `a` 的最早层也是一个层。故 `a` 的成员 `x` 落在塔在 `a` 自身层处的层里：传递性把隶属从集合搬进容纳该集合的那一层。
<!--ja-->
段階は推移的であり、`a` の最初の段階もまた段階である。だから `a` の要素 `x` は、塔の `a` 自身の段階での層の中にある。推移性が所属を、集合からその集合を収める層へ運ぶのである。
<!--/-->

```agda
stage-below₂ : (a : S) (p : ⟨ isL a ⟩) (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ a ⟩
             → ⟨ y ∈ˢ Lset (stage a p) ⟩
stage-below₂ a p x y y∈x x∈a =
  layer-trans (Lset-layer (stage a p)) y∈x (stage-below a p x x∈a)
```

<!--en-->
Transitivity applied twice reaches two levels down: a member of a member of
`a` lies in the same level, because it lies in `x` and `x` lies in the level.
<!--zh-->
传递性应用两次即可下探两层：`a` 的成员的成员落在同一层里，因为它属于 `x`，而 `x` 属于那一层。
<!--ja-->
推移性を二度適用すれば、二層下まで届く。`a` の要素の要素も同じ層の中にある。それは `x` に属し、`x` はその層に属するからである。
<!--/-->

```agda
stageBound : (a : S) (p : ⟨ isL a ⟩)
           → Σ[ β ∈ S ] (IsOrd β × ⟨ ω ∈ˢ β ⟩ × ⟨ stage a p ∈ˢ β ⟩)
stageBound a p = bound2 ω (stage a p) ω-ord (stage-ord a p)
```

<!--en-->
The two ordinals that must be dominated are the limit level `ω` and the set's
own earliest stage; `bound2` returns a single ordinal above both, with its
ordinality certified.
<!--zh-->
必须被支配的两个序数是极限层 `ω` 与该集合自身的最早层；`bound2` 返回一个同时高于两者的序数，并附带其序数性证书。
<!--ja-->
支配されなければならない二つの順序数は、極限段階 `ω` と集合自身の最初の段階である。`bound2` は両方の上にある一つの順序数を、その順序数性の証明とともに返す。
<!--/-->

```agda
bound-below₂ : (a : S) (p : ⟨ isL a ⟩) (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ a ⟩
             → ⟨ y ∈ˢ Lset (stageBound a p .fst) ⟩
bound-below₂ a p x y y∈x x∈a =
  Lset-mono (stageBound a p .snd .snd .snd) (stage-below₂ a p x y y∈x x∈a)
```

<!--en-->
Monotonicity of the tower lifts the two-level fact from the earliest stage into
the stage of the bounding ordinal. One level now holds `a`, its members, their
members, and the formula codes the comparison reads.
<!--zh-->
塔的单调性把「下探两层」的事实从最早层提升到界序数的层。现在这一层同时容纳 `a`、它的成员、成员的成员，以及比较所要读取的公式码。
<!--ja-->
塔の単調性が、二層下の事実を最初の段階から、界順序数の段階へ引き上げる。今や一つの層が、`a` とその要素、その要素の要素、そして比較が読む論理式の符号を同時に収める。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The chapter's reusable outputs are the unique predecessor of a least stage,
when that stage is a successor, and a bounding ordinal large enough for the
choice construction. The least-stage lemma is conditional, and the condition is
its content. For a property of ordinals with least stage `σ`, the property may
well hold first at the zero ordinal, and then there is nothing below to carve.
When a carve at `σ` merely exists, an ordinal below `σ` at whose successor the
property already holds, `carveAt`{.Agda} produces it, `predOf`{.Agda} turns it
into the unique predecessor by closing the truncation on
`isPropPredOf`{.Agda}, and `ord-suc-inj`{.Agda} is why a successor determines
what it succeeds. `stageBound`{.Agda} supplies the bounding ordinal: above a
set's own stage, hence above its members and theirs, and above the tower's
limit level, where the formula codes live.

<!--zh-->
本章可复用的结果，是最小层为后继时的唯一前一层，以及足以承载选择构造的上界序数。最小层引理是带条件的，而条件正是它的内容。对以 `σ` 为最小层的某条序数性质而言，性质完全可能恰在零序数处首次成立，此时其下无可雕出之物。当 `σ` 处的雕出仅仅存在，即有低于 `σ` 的序数使其后继已具该性质时，`carveAt`{.Agda} 产出雕出，`predOf`{.Agda} 按 `isPropPredOf`{.Agda} 闭合截断，把它化为唯一的前一层；而 `ord-suc-inj`{.Agda} 正是「后继决定它所后继者」的理由。`stageBound`{.Agda} 给出上界序数：它在一个集合自身的层之上，从而在其成员及其成员之上，也在塔的极限层之上，而公式码恰在那里。
<!--ja-->
本章の再利用可能な成果は、最小段階が後者である場合のその一意な直前の段階と、選択の構成を支えるのに十分な上界順序数である。最小段階の補題は条件付きであり、その条件こそが内容である。順序数の性質の最小の段階を `σ` とすると、性質は零順序数ではじめて成立してもよく、そのときは下に切り出すべきものが何もない。`σ` での切り出しが単に存在するならば、すなわち `σ` の下の順序数で、その後者がすでに性質をもつものがあれば、`carveAt`{.Agda} がそれを作り、`predOf`{.Agda} が `isPropPredOf`{.Agda} で切り詰めを閉じて、それを一意な直前の段階に変える。後者がその後者とするものを決める理由は `ord-suc-inj`{.Agda} である。`stageBound`{.Agda} が上界の順序数を供給する。それは集合自身の段階の上にあり、したがってその要素やそのまた要素の上にあり、塔の極限段階、すなわち論理式の符号が住む段階の上にもある。
<!--/-->
