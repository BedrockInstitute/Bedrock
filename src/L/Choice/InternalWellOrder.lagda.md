```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# The internal stage-order relation
<!--zh-->
# 内部层序关系
<!--ja-->
# 内部の段階順序関係
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
The construction is carried out at an arbitrary universe level and assumes excluded middle only at the displayed successor level. All later relation sets inherit precisely this standing hypothesis.
<!--zh-->
构造在任意宇宙层级上进行，只假设所标明后继层级上的排中律。后文所得的关系集恰好继承这一常设假设。
<!--ja-->
構成は任意の宇宙レベルで行い、表示された後続レベルでの排中律だけを仮定する。後で得られる関係集合が引き継ぐのは、ちょうどこの仮定である。
<!--/-->

```agda
module L.Choice.InternalWellOrder {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ; Lset-suc )
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( stageBound )
open import L.Choice.StageOrders {ℓ} lem
  using ( Mem; New; relOf; carry; orderAt; Under
        ; stepAt-fill; stepAt-read; IsLeastName; leastNameOf )
open import L.Choice.CanonicalNames {ℓ} lem using ( module Naming )
open import L.Choice.NameComparison {ℓ} lem using ( StepAt )
open import L.Choice.OrderTable {ℓ} lem using ( IsRel; ixRel-fill; ixRel-rep )
open import L.Choice.StageOrderAdequacy {ℓ} lem
  using ( CodesAt; CodesAt-in; CodesAt-out; stepOrder; module Ordered
        ; towerS; towerS-fst; powS; powS-fst; sh2; sh3; StpOut; StpIn )
open import L.Choice.NameComparisonAdequacy {ℓ} lem using ( module At )
open import L.Choice.EarliestDisagreement {ℓ} lem
  using ( codeOrder; codeOrder-fill; codeOrder-rep )
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.DefinablePowerSet {ℓ} lem using ( DefAt; DefAt-stage )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
import FOL.Absoluteness
```

<!--en-->

At each constructible stage, `orderAt`{.Agda} already gives a host-level strict well-order of its members. The task here is to make the underlying comparison available to formulas interpreted in `L`: for each ordinal stage, we obtain a relation set whose ordered-pair members correspond in both directions to `relOf (orderAt α oα)`{.Agda}. This constructs no new well-order and proves no object-language formula saying that the relation is a well-order.
<!--zh-->

在每个可构造层，`orderAt`{.Agda} 已经给出其成员上的宿主层严格良序。本章的任务是让解释于 `L` 中的公式也能使用其底层比较：对每个序数层，得到一个关系集，使其中的有序对成员与 `relOf (orderAt α oα)`{.Agda} 逐对双向对应。这里既不构造新的良序，也不证明断言该关系为良序的对象语言公式。
<!--ja-->

各構成可能段階では、`orderAt`{.Agda} がその要素上のホスト側の狭義整列順序をすでに与えている。この章の課題は、その基礎となる比較を `L` で解釈される論理式からも使えるようにすることである。各順序数段階について、順序対の所属が `relOf (orderAt α oα)`{.Agda} と対ごとに両方向で対応する関係集合を得る。ここで新しい整列順序を構成することも、この関係が整列順序であると述べる対象言語の論理式を証明することもない。
<!--/-->

<!--en-->
The distinction between the two levels will guide the chapter. The well-order is a mathematical structure in the host theory, whereas its representative inside `L` must be a set that the first-order language can mention.
<!--zh-->
本章始终区分两个层面。良序是宿主理论中的数学结构，而它在 `L` 内的表示必须是第一阶语言能够指称的集合。
<!--ja-->
この章では二つの水準を一貫して区別する。整列順序はホスト理論の数学的構造であるが、`L` の内部でそれを表すものは、一階言語から指すことのできる集合でなければならない。
<!--/-->



<!--en-->
To describe one comparison step internally, it suffices to combine variables and constants with membership, equality, conjunction, and existential quantification. The six existential binders introduced below are repeated uses of this one logical constructor.
<!--zh-->
要在内部描述一次比较步，只须用隶属、等词、合取与存在量化连接变元和常元。下文的六个存在绑定，是对同一个逻辑构造器的反复使用。
<!--ja-->
一回の比較ステップを内部で記述するには、変数と定数を、所属・等号・連言・存在量化で結べば十分である。以下の六つの存在束縛は、同じ論理構成子を繰り返し用いたものである。
<!--/-->

<!--en-->
The relation will be indexed by an ordinal stage. Its witnesses must therefore be recognized as constructible sets, and successor-stage membership must be related to definability over the preceding stage.
<!--zh-->
这个关系以序数层为指标。因此，它的见证必须被辨认为可构造集合，而后继层中的隶属必须与前一层上的可定义性联系起来。
<!--ja-->
この関係は順序数段階を添字とする。そのため、証人は構成可能集合として同定され、後続段階への所属は直前の段階上での定義可能性と結び付けられなければならない。
<!--/-->

<!--en-->
The semantic target has two distinct levels. `orderAt δ od`{.Agda} is the host-level strict well-order on the members of `Lset δ`{.Agda}. For the equal-birth step used in its recursive description, `Under δ (stepOrder δ od) u v`{.Agda} records that `u` and `v` belong to `Lset (sucV δ)`{.Agda} and that the resulting members are related by `stepOrder δ od`{.Agda}. Least names over `Lset δ`{.Agda} connect this host-level step to the formula constructed below.
<!--zh-->
语义目标分属两个层面。`orderAt δ od`{.Agda} 是 `Lset δ`{.Agda} 的成员上的宿主层严格良序。为了描述其递归构造中的同生步进，`Under δ (stepOrder δ od) u v`{.Agda} 记录 `u`、`v` 属于 `Lset (sucV δ)`{.Agda}，并记录由此得到的两个成员满足 `stepOrder δ od`{.Agda}。`Lset δ`{.Agda} 上的最小名字把这项宿主层步进连接到下文构造的公式。
<!--ja-->
意味論的な目標には二つの水準がある。`orderAt δ od`{.Agda} は、`Lset δ`{.Agda} の要素上のホスト側の狭義整列順序である。その再帰的記述で用いる同じ誕生段階のステップについて、`Under δ (stepOrder δ od) u v`{.Agda} は、`u` と `v` が `Lset (sucV δ)`{.Agda} に属することと、そこから得られる二要素が `stepOrder δ od`{.Agda} で関係づけられることを記録する。`Lset δ`{.Agda} 上の最小名が、このホスト側のステップを以下で構成する論理式へ結び付ける。
<!--/-->

<!--en-->
The recursive order table already knows how to turn an adequate step description into a relation set. What remains is to give one concrete formula and prove its two semantic directions, so that the table no longer depends on an abstract step parameter.
<!--zh-->
递归序表已经知道怎样把一条充分的步进描述变成关系集。剩下的工作是给出一条具体公式，并证明它的两个语义方向，从而消去序表对抽象步进参数的依赖。
<!--ja-->
再帰的な順序表には、妥当なステップ記述から関係集合を作る仕組みがすでにある。残る仕事は、具体的な論理式を一つ与えてその意味論的な二方向を証明し、抽象的なステップ引数への順序表の依存を取り除くことである。
<!--/-->

<!--en-->
That formula must recognize four moving objects: the stage tower, its definable subsets, the table value at the stage, and the codes over the tower. These recognition clauses let an arbitrary satisfying assignment be converted back into the intended mathematical data.
<!--zh-->
该公式必须辨认四个随层变化的对象：层塔、它的可定义子集、表在该层的取值，以及塔上的码。借助这些辨认子句，任意满足赋值都能被还原为预期的数学资料。
<!--ja-->
この論理式は、段階の塔、その定義可能部分集合、段階における表の値、塔上のコードという四つの変動する対象を同定しなければならない。これらの同定条件により、任意の充足する割り当てを意図した数学的データへ戻せる。
<!--/-->

<!--en-->
Two further witnesses are fixed constants: the comparison relation on codes and the code set for the empty alphabet. Together with the moving relation value from the table, they supply the auxiliary relations and domains used when least names are compared.
<!--zh-->
另有两个见证被固定为常元：码上的比较关系与空字母表的码集。它们与序表给出的可变关系值一道，提供比较最小名字时所需的辅助关系与定义域。
<!--ja-->
さらに二つの証人は固定された定数である。コード上の比較関係と、空のアルファベットに対するコード集合である。これらは順序表から得る変動する関係値とともに、最小名を比較するための補助関係と領域を与える。
<!--/-->

<!--en-->
Satisfaction is interpreted in the propositional structure of constructible sets. Consequently, each existential clause yields a propositionally truncated dependent pair: a witness may support the proof while remaining unavailable as chosen data outside the proposition.
<!--zh-->
满足关系解释在可构造集合的命题结构中。因此，每个存在子句都产生一个经过命题截断的依值对：见证可以支撑证明，却不能作为已选资料从命题之外取出。
<!--ja-->
充足関係は構成可能集合の命題的構造で解釈される。したがって、各存在節は命題的に切り詰められた依存対を生む。証人は証明を支えるが、命題の外で選択済みのデータとして取り出すことはできない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
```

<!--en-->
The comparison takes place among members of a successor stage. Presenting a stage by a small type lets the host well-order act on its members, while `sucV`{.Agda} records the successor ordinal used to locate the two compared objects.
<!--zh-->
比较发生在某个后继层的成员之间。把层呈现为小类型，使宿主良序能够作用于其成员；`sucV`{.Agda} 则记录定位两个被比较对象所用的后继序数。
<!--ja-->
比較は後続段階の要素の間で行われる。段階を小さい型で表示することで、ホスト側の整列順序をその要素に作用させられる。`sucV`{.Agda} は、比較される二対象を位置付ける後続順序数を記録する。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
```

<!--en-->
From this point on, formulas are evaluated in the first-order structure carried by `L`. Thus an element used in a slot contains both its underlying set and the proposition that the set is constructible.
<!--zh-->
从这里起，公式都解释在 `L` 所携带的第一阶结构中。因此，放入槽位的元素既包含底层集合，也包含该集合可构造这一命题。
<!--ja-->
ここから先、論理式は `L` が備える一階構造で解釈される。したがって、スロットに置く要素は、その基礎集合と、その集合が構成可能であるという命題の両方を含む。
<!--/-->

```agda
open hPropStructure 𝒮ʟ
```

<!--en-->
We write `γ ⊨ φ`{.Agda} for this interpretation. Absoluteness permits the recognition formulas to be read as concrete facts about the underlying sets, which is what makes the later unpacking possible.
<!--zh-->
以下用 `γ ⊨ φ`{.Agda} 表示这种解释。绝对性使各条辨认公式能够被读成关于底层集合的具体事实，这正是后文能够拆出见证的原因。
<!--ja-->
以下では、この解釈を `γ ⊨ φ`{.Agda} と書く。絶対性によって、同定論理式を基礎集合についての具体的事実として読めるため、後で証人を読み解くことができる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The elements the description binds
<!--zh-->
## 描述所绑定的诸元素
<!--ja-->
## 記述が束縛する要素
<!--/-->

<!--en-->
The six-slot shift moves every variable past the six existential witnesses of the step formula.
<!--zh-->
六槽移位把每个变元移过步进公式的六个存在见证。
<!--ja-->
六つの枠のずらしは、すべての変数を、ステップの論理式の六つの証人の向こう側へ運ぶ。
<!--/-->

```agda
private
  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))
```

<!--en-->
After all six witnesses have been bound, `StepAt`{.Agda} directly refers to five of them: the tower `tw`, the table relation `rl`, the code set `cs`, the code order `ro`, and the empty-alphabet code set `c0`. The definable-power-set witness `pw` is used by the surrounding membership clauses rather than passed to `StepAt`{.Agda}.
<!--zh-->
六个见证全部绑定后，`StepAt`{.Agda} 直接引用其中五个：塔 `tw`、表关系 `rl`、码集 `cs`、码序 `ro` 与空字母表码集 `c0`。可定义幂集见证 `pw` 用于外围的隶属子句，并不传给 `StepAt`{.Agda}。
<!--ja-->
六つの証人をすべて束縛した後、`StepAt`{.Agda} はそのうち五つを直接参照する。塔 `tw`、表の関係 `rl`、コード集合 `cs`、コード順序 `ro`、空のアルファベットのコード集合 `c0` である。定義可能冪集合の証人 `pw` は周囲の所属条件で使われ、`StepAt`{.Agda} には渡されない。
<!--/-->

```agda
  iTow iRel iCod iOrd iNil
    : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  iTow = suc (suc (suc (suc (suc zero))))
  iRel = suc (suc (suc zero))
  iCod = suc (suc zero)
```

<!--en-->
The two nearest indices select `ro` and `c0`. They do not introduce further binders; they only record where these already bound witnesses occur in the fully extended environment.
<!--zh-->
最内侧的两个指标选取 `ro` 与 `c0`。它们不引入新的绑定，只记录这两个已绑定见证在完全扩张的环境中所处的位置。
<!--ja-->
最も内側の二つの添字は `ro` と `c0` を選ぶ。新たな束縛を導入するのではなく、すでに束縛された二つの証人が、完全に拡張された環境のどこにあるかを記録するだけである。
<!--/-->

```agda
  iOrd = suc zero
  iNil = zero
```

<!--en-->
## The description
<!--zh-->
## 那条描述
<!--ja-->
## ステップの論理式
<!--/-->

<!--en-->
The six witnesses of `Stp d f u v`{.Agda} are introduced in dependency order. First comes a tower recognized at stage `d`; next comes its definable power set, whose membership clauses will certify that the objects at `u` and `v` are available for the successor-stage comparison.
<!--zh-->
`Stp d f u v`{.Agda} 的六个见证按依赖顺序引入。首先是被辨认为 `d` 所指层的塔；其次是它的可定义幂集，其中的隶属子句将证明 `u` 与 `v` 所指对象可以参加后继层比较。
<!--ja-->
`Stp d f u v`{.Agda} の六つの証人は、依存関係に従う順序で導入される。最初は `d` が指す段階の塔であり、次はその定義可能冪集合である。後者への所属条件が、`u` と `v` の指す対象を後続段階で比較できることを保証する。
<!--/-->

```agda
opaque
  Stp : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  Stp d f u v =
    ∃̇ ( LsetGraphAt zero (suc d)
      ∧̇ ∃̇ ( DefAt zero (suc zero)
```

<!--en-->
The third witness is a value `rl` recorded by the table at the stage, and the fourth is the code set over the tower. The last two witnesses are variables constrained by object equality to be the canonical code order and the code set for the empty alphabet.
<!--zh-->
第三个见证是序表在该层记录的取值 `rl`，第四个是塔上的码集。最后两个见证是由对象等词约束的变元，分别被固定为典范码序与空字母表的码集。
<!--ja-->
第三の証人は、その段階で順序表に記録された値 `rl` であり、第四の証人は塔上のコード集合である。最後の二証人は対象言語の等号で制約される変数で、それぞれ正準なコード順序と空のアルファベットに対するコード集合に固定される。
<!--/-->

```agda
           ∧̇ ( (var (sh2 u) ∈̇ var zero)
             ∧̇ ( (var (sh2 v) ∈̇ var zero)
               ∧̇ ∃̇ ( appAt (sh3 f) (sh3 d) zero
                    ∧̇ ∃̇ ( CodesAt zero (sh3 zero)
                         ∧̇ ∃̇ ( (var zero ≐ con codeOrder)
```

<!--en-->
At the innermost point, `StepAt`{.Agda} sees seven semantic slots: the five auxiliary witnesses selected above and the two original objects shifted past all six binders. It asserts the comparison of their least names; it does not assert that the represented relation satisfies a well-order formula inside `L`.
<!--zh-->
到达最内层时，`StepAt`{.Agda} 看见七个语义槽位：上面选出的五个辅助见证，以及越过全部六个绑定后的两个原有对象。它断言二者最小名字之间的比较，并不在 `L` 内断言所表示的关系满足良序公式。
<!--ja-->
最内部では、`StepAt`{.Agda} は七つの意味論的スロットを見る。上で選んだ五つの補助証人と、六つの束縛を越えてずらされた二つの元の対象である。そこで述べるのは両者の最小名の比較であり、表現された関係が `L` の内部で整列順序の論理式を満たすという主張ではない。
<!--/-->

```agda
                              ∧̇ ∃̇ ( (var zero ≐ con (AllCodes ∅ʟ))
                                   ∧̇ StepAt iOrd iRel iTow iCod iNil
                                       (sh6 u) (sh6 v) ) ) ) ) ) ) ) )
```

<!--en-->
## The six binders, layer by layer
<!--zh-->
## 六个绑定，逐层展开
<!--ja-->
## 六つの束縛を層ごとに扱う
<!--/-->

<!--en-->
The reading module fixes the four slots, the environment, and the ordinalness of the decoded stage, since the host order needs that ordinalness.
<!--zh-->
读取模块固定四个槽位、环境，以及被解码层的序数性，因为宿主序需要该序数性。
<!--ja-->
読みのモジュールは、四つの枠・環境・そして解読された段階の順序数性を固定する。ホストの順序がその順序数性を必要とするからである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Reading {n : ℕ} (d f u v : Fin n) (γ : S ^ n)
               (od : IsOrd (fst (lookup d γ))) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    δ : V ℓ
    δ = fst (lookup d γ)
```

<!--en-->
The host order is carried onto the presentation of the stage: the strict order of the members is available on the small index type.
<!--zh-->
宿主序被搬运到层的呈现上：成员的严格序可在小索引类型上取用。
<!--ja-->
ホストの順序は、段階の提示の上に運ばれる。要素の狭義の順序が、小さな索引型の上で使えるのである。
<!--/-->

```agda
    ordW : SWO ⟪ Lset δ ⟫
    ordW = carry (Lset δ) (orderAt δ od)
```

<!--en-->
A name for a set in `Lset (sucV δ)`{.Agda} is formed over `Lset δ`{.Agda} and becomes distinguished as least only relative to the carried order `ordW`{.Agda} on that preceding stage. The predicate `IsLeastName`{.Agda} records both that the name denotes the given set and that no competing name is smaller. This is the precise bridge between sets in the successor stage and the name comparison used by `StepAt`{.Agda}.
<!--zh-->
`Lset (sucV δ)`{.Agda} 中集合的名字在 `Lset δ`{.Agda} 上形成，并且只有相对于前一层上搬运后的序 `ordW`{.Agda} 才能被选定为最小名字。谓词 `IsLeastName`{.Agda} 同时记录该名字解释为给定集合，以及没有更小的竞争名字。这正是后继层中的集合与 `StepAt`{.Agda} 所用名字比较之间的精确桥梁。
<!--ja-->
`Lset (sucV δ)`{.Agda} にある集合の名前は `Lset δ`{.Agda} 上で作られ、その直前の段階に移された順序 `ordW`{.Agda} に関してのみ最小名として区別される。述語 `IsLeastName`{.Agda} は、その名前が与えられた集合を表すことと、それより小さい別の名前がないことの両方を記録する。これが、後続段階の集合と `StepAt`{.Agda} が用いる名前比較との正確な橋渡しである。
<!--/-->

```agda
    module NM = Naming (Lset δ) ordW
```

<!--en-->
The semantic goal is the propositionally truncated `Under`{.Agda} statement. It contains both successor-stage memberships and the step comparison, but reading the existential formula establishes only that such evidence exists; it does not choose names or any of the six bound objects as data.
<!--zh-->
语义目标是经过命题截断的 `Under`{.Agda} 陈述。它同时包含两个后继层隶属事实与步进比较，但读取存在公式只会证明这类证据存在，并不会把名字或六个绑定对象中的任何一个选作资料。
<!--ja-->
意味論的な目標は、命題的に切り詰められた `Under`{.Agda} の主張である。そこには二つの後続段階への所属とステップ比較が含まれるが、存在論理式を読むことで分かるのは、そのような証拠が存在することだけである。名前や六つの束縛対象をデータとして選ぶことはない。
<!--/-->

```agda
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ)) ∥₁
```

<!--en-->
After all six witnesses have extended the environment, `StepHolds tw pw rl cs ro c0`{.Agda} is exactly the satisfaction of the innermost `StepAt`{.Agda} formula. It is the final semantic condition inside the six existential layers. The surrounding binders, rather than `StepHolds`{.Agda} itself, place the successive witnesses under propositional truncation.
<!--zh-->
六个见证全部扩张环境后，`StepHolds tw pw rl cs ro c0`{.Agda} 恰好表示最内层 `StepAt`{.Agda} 公式的满足。它是六层存在结构内部的最终语义条件。把各层见证置于命题截断之下的是外围绑定，而不是 `StepHolds`{.Agda} 本身。
<!--ja-->
六つの証人で環境をすべて拡張した後、`StepHolds tw pw rl cs ro c0`{.Agda} は、最内部の `StepAt`{.Agda} 論理式が充足されることそのものである。これは六つの存在の層の内側にある最後の意味論的条件である。各層の証人を命題的切り詰めの下に置くのは周囲の束縛子であり、`StepHolds`{.Agda} 自体ではない。
<!--/-->

```agda
    opaque
      StepHolds : (tw pw rl cs ro c0 : S) → Type (ℓ-suc ℓ)
      StepHolds tw pw rl cs ro c0 =
        ⟨ (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ)
          ⊨ StepAt iOrd iRel iTow iCod iNil (sh6 u) (sh6 v) ⟩
```

<!--en-->
The innermost payload contains the equation fixing `c0` and the step satisfaction itself. These are ordinary conjunctive evidence inside the payload; the propositional truncation is introduced by the surrounding existential layer.
<!--zh-->
最内层载荷包含固定 `c0` 的等式与步进满足本身。二者在载荷内部是普通的合取证据；命题截断由外围存在层引入。
<!--ja-->
最内部のペイロードは、`c0` を固定する等式とステップの充足そのものを含む。これらはペイロード内では通常の連言の証拠であり、命題的切り詰めは外側の存在層によって導入される。
<!--/-->

```agda
    Six : (tw pw rl cs ro c0 : S) → Type (ℓ-suc ℓ)
    Six tw pw rl cs ro c0 =
        ⟨ (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ (var zero ≐ con (AllCodes ∅ʟ)) ⟩
      × StepHolds tw pw rl cs ro c0
```

<!--en-->
One layer outward, `ro` is fixed to the canonical code order, while the existence of a suitable `c0` is propositionally truncated. Equality determines the intended underlying set, but the proof does not expose a selected existential witness.
<!--zh-->
向外一层，`ro` 被固定为典范码序，而合适的 `c0` 的存在经过命题截断。等式确定了预期的底层集合，但证明不会暴露一个已选的存在见证。
<!--ja-->
一層外では、`ro` が正準なコード順序に固定され、適切な `c0` の存在は命題的に切り詰められる。等式は意図した基礎集合を定めるが、証明が選択済みの存在証人を公開することはない。
<!--/-->

```agda
    Five : (tw pw rl cs ro : S) → Type (ℓ-suc ℓ)
    Five tw pw rl cs ro =
        ⟨ (ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ (var zero ≐ con codeOrder) ⟩
      × ∥ (Σ[ c0 ∶ S ] Six tw pw rl cs ro c0) ∥₁
```

<!--en-->
The code-set clause characterizes `cs` over the bound tower. When the formula is read, its adequacy and the earlier identification of the tower determine the underlying set of `cs`; the remaining inner witnesses still stay under propositional truncation.
<!--zh-->
码集子句刻画绑定塔上的 `cs`。读取公式时，它的充分性与先前对塔的辨认共同确定 `cs` 的底层集合；其余内层见证仍留在命题截断之下。
<!--ja-->
コード集合の条件は、束縛された塔上の `cs` を特徴付ける。論理式を読むとき、その妥当性と先に得た塔の同定から `cs` の基礎集合が定まる。残る内側の証人は、なお命題的切り詰めの下にある。
<!--/-->

```agda
    Four : (tw pw rl cs : S) → Type (ℓ-suc ℓ)
    Four tw pw rl cs =
        ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
      × ∥ (Σ[ ro ∶ S ] Five tw pw rl cs ro) ∥₁
```

<!--en-->
The table-application clause says that `rl` is some value recorded at the decoded stage. In the reading direction `rl` is arbitrary among such recorded values, a fact that later forces the relation hypothesis to quantify over every value there; in the filling direction a particular supplied `rl` is used.
<!--zh-->
序表应用子句说明 `rl` 是被解码层处记录的某个取值。在读取方向，`rl` 可以是该处任意一个被记录值，因此后面的关系假设必须对该处每个取值作全称陈述；在填充方向，则使用调用方给出的某个特定 `rl`。
<!--ja-->
順序表の適用条件は、`rl` が復号された段階で記録された何らかの値であることを述べる。読み出す向きでは、`rl` はそこで記録された任意の値であり得るため、後の関係仮定はそのすべての値を全称的に扱う必要がある。埋める向きでは、与えられた特定の `rl` を使う。
<!--/-->

```agda
    Three : (tw pw rl : S) → Type (ℓ-suc ℓ)
    Three tw pw rl =
        ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
      × ∥ (Σ[ cs ∶ S ] Four tw pw rl cs) ∥₁
```

<!--en-->
The definable-power-set clause identifies `pw`, and the next two conjuncts place both compared objects in it. Once `tw` and `pw` have been identified, these memberships become membership in `Lset (sucV δ)`{.Agda}, supplying the two domain components required by `Under`{.Agda}.
<!--zh-->
可定义幂集子句辨认 `pw`，随后的两个合取项把两个被比较对象都放入其中。一旦 `tw` 与 `pw` 被确定，这两条隶属便转化为对 `Lset (sucV δ)`{.Agda} 的隶属，给出 `Under`{.Agda} 所需的两个定义域分量。
<!--ja-->
定義可能冪集合の条件が `pw` を同定し、続く二つの連言が比較対象をともにそこへ置く。`tw` と `pw` が同定されれば、これらの所属は `Lset (sucV δ)`{.Agda} への所属となり、`Under`{.Agda} が必要とする二つの領域成分を与える。
<!--/-->

```agda
    Two : (tw pw : S) → Type (ℓ-suc ℓ)
    Two tw pw =
        ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      × ( ⟨ fst (lookup u γ) ∈ fst pw ⟩
        × ( ⟨ fst (lookup v γ) ∈ fst pw ⟩
```

<!--en-->
After those memberships, the remaining payload begins with the truncated existence of the table value `rl`. The eventual target `Goal`{.Agda} is itself a proposition, so the proof may eliminate each truncation into that target without extracting a reusable choice of witness.
<!--zh-->
在两条隶属之后，剩余载荷从表值 `rl` 的截断存在开始。最终目标 `Goal`{.Agda} 本身是命题，因此证明可以把每层截断消去到这个目标中，而不会抽取出可重复使用的见证选择。
<!--ja-->
二つの所属の後、残るペイロードは表の値 `rl` の切り詰められた存在から始まる。最終目標 `Goal`{.Agda} 自体が命題なので、再利用できる証人の選択を取り出すことなく、各切り詰めをこの目標へ消去できる。
<!--/-->

```agda
          × ∥ (Σ[ rl ∶ S ] Three tw pw rl) ∥₁ ) )
```

<!--en-->
The outermost payload starts with a witness `tw` satisfying the stage graph. Ordinality makes that description unique at the level of underlying sets, so an arbitrary satisfying `tw` can be identified with `Lset δ`{.Agda}; the nested existence of all later witnesses remains propositionally truncated.
<!--zh-->
最外层载荷从满足层图的见证 `tw` 开始。序数性使这条描述在底层集合层面唯一，因此任意满足它的 `tw` 都能与 `Lset δ`{.Agda} 同一视；后续所有见证的嵌套存在仍经过命题截断。
<!--ja-->
最外部のペイロードは、段階グラフを満たす証人 `tw` から始まる。順序数性により、この記述は基礎集合の水準で一意なので、任意の充足する `tw` を `Lset δ`{.Agda} と同定できる。後続するすべての証人の入れ子の存在は、命題的に切り詰められたままである。
<!--/-->

```agda
    One : (tw : S) → Type (ℓ-suc ℓ)
    One tw = ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
           × ∥ (Σ[ pw ∶ S ] Two tw pw) ∥₁
```

<!--en-->
## The step adequacy at a stage
<!--zh-->
## 层处的那一步之充分性
<!--ja-->
## 段階におけるステップの妥当性
<!--/-->

<!--en-->
Only five of the six bound elements enter `StepAt`{.Agda}; `pw` serves the two surrounding membership clauses. Accordingly, `Slots`{.Agda} identifies the tower and code set with their intended values, assumes that `rl` has the pairwise representation property `IsRel δ rl`{.Agda}, and fixes `ro` and `c0` to the two required constants. These facts are exactly what the earlier name-comparison adequacy theorem needs.
<!--zh-->
六个绑定元素中只有五个进入 `StepAt`{.Agda}；`pw` 用于外围的两项隶属子句。因此，`Slots`{.Agda} 把塔与码集认同为预期对象，假设 `rl` 具有逐对表示性质 `IsRel δ rl`{.Agda}，并把 `ro` 与 `c0` 固定为所需的两个常元。这些事实恰是先前名字比较充分性定理所需的条件。
<!--ja-->
六つの束縛要素のうち `StepAt`{.Agda} に入るのは五つだけであり、`pw` はその外側にある二つの所属条件で使われる。そこで `Slots`{.Agda} は、塔と符号集合を意図した対象と同一視し、`rl` が対ごとの表現性 `IsRel δ rl`{.Agda} をもつと仮定し、`ro` と `c0` を必要な二つの定数に固定する。これらは、先に証明した名前比較の妥当性定理が必要とする条件そのものである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Slots (tw pw rl cs ro c0 : S)
               (qtw : fst tw ≡ Lset δ)
               (hrel : IsRel δ rl)
               (qcs : fst cs ≡ fst (AllCodes (LsetS δ od)))
               (qro : fst ro ≡ fst codeOrder)
               (qc0 : fst c0 ≡ fst (AllCodes ∅ʟ)) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Inside the alignment, the naming adequacy is instantiated at the stage, and its local step comparison is opened with the code order and the relation value, both directions of whose representation are supplied.
<!--zh-->
在对齐内部，命名充分性在该层处实例化；其局部步进比较以码序与关系值打开，而关系表示的两个方向一并供给。
<!--ja-->
整合の内部では、名前づけの妥当性が段階のもとで具体化され、その局所の一歩の比較が、コードの順序と関係の値のもとで開かれる。関係の表現の両方向が供給される。
<!--/-->

```agda
    private module A6 = At (Lset δ) (snd (LsetS δ od)) ordW
    private module L6 = A6.Least codeOrder rl codeOrder-rep codeOrder-fill
                          (ixRel-rep δ od rl hrel) (ixRel-fill δ od rl hrel)
```

<!--en-->
With those certifications, the name-comparison theorem is instantiated in the fully extended environment. Its seven semantic slots are the two compared objects together with the five auxiliary witnesses selected by `iTow`{.Agda}, `iRel`{.Agda}, `iCod`{.Agda}, `iOrd`{.Agda}, and `iNil`{.Agda}.
<!--zh-->
有了这些证明，名字比较定理便可在完全扩张的环境中实例化。它的七个语义槽位由两个被比较对象与五个辅助见证组成，后者分别由 `iTow`{.Agda}、`iRel`{.Agda}、`iCod`{.Agda}、`iOrd`{.Agda}、`iNil`{.Agda} 选出。
<!--ja-->
これらの保証により、名前比較の定理を完全に拡張された環境で具体化できる。その七つの意味論的スロットは、比較される二対象と、`iTow`{.Agda}、`iRel`{.Agda}、`iCod`{.Agda}、`iOrd`{.Agda}、`iNil`{.Agda} が選ぶ五つの補助証人からなる。
<!--/-->

```agda
    private module St = L6.Step iOrd iRel iTow iCod iNil (sh6 u) (sh6 v)
              (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ)
              qro refl (Σ≡Prop (λ x → snd (isL x)) qtw) qcs qc0
```

<!--en-->
For the first object, `LeastFst t`{.Agda} is the local form of the assertion that `t` is its least name. Its denotation equation is oriented oppositely from the corresponding equation in `IsLeastName`{.Agda}; the conversion lemmas below reverse that equation while preserving the same minimality claim.
<!--zh-->
对第一个对象，`LeastFst t`{.Agda} 是「`t` 是它的最小名字」这一断言的局部形式。其中的解释等式与 `IsLeastName`{.Agda} 中相应等式方向相反；下文的转换引理反转该等式，同时保留同一项极小性断言。
<!--ja-->
第一の対象について、`LeastFst t`{.Agda} は「`t` がその最小名である」という主張の局所的な形である。そこに含まれる表示の等式は、`IsLeastName`{.Agda} の対応する等式とは逆向きである。以下の変換補題は、その等式を反転しながら同じ最小性の主張を保つ。
<!--/-->

```agda
    LeastFst : NM.Name → Type (ℓ-suc ℓ)
    LeastFst = St.LeastOf (sh6 u)
```

<!--en-->
`LeastSnd`{.Agda} gives the same bridge for the second object. Keeping the two predicates parallel matters because `StepAt`{.Agda} compares one least name with the other rather than merely asserting that least names exist.
<!--zh-->
`LeastSnd`{.Agda} 为第二个对象给出同样的桥梁。保持两个谓词平行很重要，因为 `StepAt`{.Agda} 比较的是两个最小名字，而不只是断言最小名字存在。
<!--ja-->
`LeastSnd`{.Agda} は第二の対象について同じ橋渡しを与える。`StepAt`{.Agda} は最小名の存在だけを述べるのではなく、一方の最小名を他方と比較するので、二つの述語を並行に保つことが必要である。
<!--/-->

```agda
    LeastSnd : NM.Name → Type (ℓ-suc ℓ)
    LeastSnd = St.LeastOf (sh6 v)
```

<!--en-->
The exported predicate `IsLeastName`{.Agda} and the adequacy theorem state the interpreting equation in opposite directions. Path symmetry converts the first object's equation, and the minimality clause is transported by reversing each competing equation in the same way.
<!--zh-->
导出的谓词 `IsLeastName`{.Agda} 与充分性定理以相反方向陈述解释等式。路径对称性转换第一个对象的等式，而极小性子句则用同样方式反转每条竞争等式来搬运。
<!--ja-->
公開された述語 `IsLeastName`{.Agda} と妥当性定理は、解釈の等式を互いに逆向きに述べる。パスの対称性で第一の対象の等式を変換し、極小性条件も各競合名の等式を同様に反転して移す。
<!--/-->

```agda
    leastFst-in : (t : NM.Name)
                → IsLeastName δ ordW t (fst (lookup u γ)) → LeastFst t
    leastFst-in t (q , mn) = sym q , λ t' q' → mn t' (sym q')
```

<!--en-->
The second object's conversion is identical in form. It changes only the orientation of equality and preserves the mathematical content of leastness.
<!--zh-->
第二个对象的转换形式完全相同。它只改变等式方向，并保留极小性的数学内容。
<!--ja-->
第二の対象の変換も同じ形である。変わるのは等式の向きだけであり、最小性の数学的内容は保たれる。
<!--/-->

```agda
    leastSnd-in : (t : NM.Name)
                → IsLeastName δ ordW t (fst (lookup v γ)) → LeastSnd t
    leastSnd-in t (q , mn) = sym q , λ t' q' → mn t' (sym q')
```

<!--en-->
In the reading direction, the same symmetry recovers `IsLeastName`{.Agda} for the first object. Since reversing a path twice restores its original orientation, this conversion loses no information.
<!--zh-->
在读取方向，同一个对称性操作恢复第一个对象的 `IsLeastName`{.Agda}。由于路径反转两次会恢复原方向，这一转换不损失信息。
<!--ja-->
読み出す向きでは、同じ対称性によって第一の対象の `IsLeastName`{.Agda} を回復する。パスを二度反転すれば元の向きに戻るので、この変換で情報は失われない。
<!--/-->

```agda
    leastFst-out : (t : NM.Name)
                 → LeastFst t → IsLeastName δ ordW t (fst (lookup u γ))
    leastFst-out t (q , mn) = sym q , λ t' q' → mn t' (sym q')
```

<!--en-->
The second least-name predicate is read back in the same way, leaving two ordinary least-name facts ready for the host-level step lemma.
<!--zh-->
第二个最小名字谓词以同样方式读回，于是得到两条普通的最小名字事实，可供宿主层步进引理使用。
<!--ja-->
第二の最小名述語も同じ方法で読み戻され、ホスト側のステップ補題に渡せる二つの通常の最小名の事実が得られる。
<!--/-->

```agda
    leastSnd-out : (t : NM.Name)
                 → LeastSnd t → IsLeastName δ ordW t (fst (lookup v γ))
    leastSnd-out t (q , mn) = sym q , λ t' q' → mn t' (sym q')
```

<!--en-->
The two semantic directions for the innermost formula are deliberately asymmetric. Given two particular least names and their comparison, `holds-in`{.Agda} proves `StepHolds`{.Agda}. From `StepHolds`{.Agda}, `holds-out`{.Agda} returns only the propositionally truncated existence of two suitable least names and their comparison, so no chosen pair escapes the formula.
<!--zh-->
最内层公式的两个语义方向有意保持不对称。给定两条具体的最小名字及其比较，`holds-in`{.Agda} 证明 `StepHolds`{.Agda}。反过来，`holds-out`{.Agda} 从 `StepHolds`{.Agda} 只得到命题截断下的存在性，即存在两条合适的最小名字及其比较，因此没有一对已选名字逸出公式。
<!--ja-->
最内部の論理式に対する二つの意味論的な向きは、意図的に非対称である。二つの具体的な最小名とその比較が与えられると、`holds-in`{.Agda} は `StepHolds`{.Agda} を証明する。逆に `holds-out`{.Agda} が `StepHolds`{.Agda} から返すのは、適切な二つの最小名とその比較が存在することの命題的切り詰めだけであり、選ばれた名前の組が論理式の外へ出ることはない。
<!--/-->

```agda
    opaque
      unfolding StepHolds
```

<!--en-->
In the inward direction, the local least-name facts for `t₁` and `t₂`, together with `t₁ ≺ₙ t₂`, supply all the semantic content of the innermost formula. The name-comparison adequacy theorem turns precisely these three facts into `StepHolds`{.Agda}.
<!--zh-->
在向内方向，`t₁`、`t₂` 的局部最小名字事实连同 `t₁ ≺ₙ t₂`，给出最内层公式所需的全部语义内容。名字比较充分性定理恰把这三项事实转成 `StepHolds`{.Agda}。
<!--ja-->
内向きでは、`t₁` と `t₂` についての局所的な最小名の事実と `t₁ ≺ₙ t₂` を合わせると、最内部の論理式に必要な意味論的内容がすべて揃う。名前比較の妥当性定理は、まさにこの三つの事実を `StepHolds`{.Agda} へ移す。
<!--/-->

```agda
      holds-in : (t₁ t₂ : NM.Name) → LeastFst t₁ → LeastSnd t₂ → NM._≺ₙ_ t₁ t₂
               → StepHolds tw pw rl cs ro c0
      holds-in = St.StepAt-fill
```

<!--en-->
Conversely, reading the innermost satisfaction yields, under propositional truncation, two least names and their name comparison. The truncation is essential: the result asserts the existence of suitable names without exporting a chosen pair.
<!--zh-->
反过来，读取最内层满足会在命题截断之下得到两个最小名字及其名字比较。这个截断不可省略：结果断言合适名字存在，却不导出一对已选名字。
<!--ja-->
逆に、最内部の充足を読むと、命題的切り詰めの下で二つの最小名とその名前比較が得られる。この切り詰めは本質的である。結果は適切な名前の存在を述べるが、選択済みの一対を公開しない。
<!--/-->

```agda
      holds-out : StepHolds tw pw rl cs ro c0
                → ∥ Σ[ t₁ ∶ NM.Name ] Σ[ t₂ ∶ NM.Name ]
                      (LeastFst t₁ × (LeastSnd t₂ × NM._≺ₙ_ t₁ t₂)) ∥₁
      holds-out = St.StepAt-read
```
</div>
</details>

<!--en-->
## Unpacking
<!--zh-->
## 拆开
<!--ja-->
## 束縛を読み解く
<!--/-->

<!--en-->
The total reading must work for whatever six witnesses a satisfying assignment provides. Its first hypotheses say that `tw` satisfies the graph description of the decoded stage, that `pw` satisfies the definable-power-set description over it, and that the first compared object belongs to `pw`; later uniqueness and adequacy results will turn these into facts about the concrete stage.
<!--zh-->
总体读取必须适用于满足赋值所给出的任意六个见证。最先的假设说明：`tw` 满足被解码层的图描述，`pw` 满足其上的可定义幂集描述，并且第一个被比较对象属于 `pw`；随后将用唯一性与充分性结果，把这些条件转成关于具体层的事实。
<!--ja-->
全体の読み出しは、充足する割り当てが与えるどの六証人に対しても働かなければならない。最初の仮定は、`tw` が復号された段階のグラフ記述を満たし、`pw` がその上の定義可能冪集合の記述を満たし、第一の比較対象が `pw` に属することを述べる。後で一意性と妥当性を使い、これらを具体的な段階についての事実へ変換する。
<!--/-->

```agda
  private
    atAll : (tw pw rl cs ro c0 : S)
          → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
          → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
          → ⟨ fst (lookup u γ) ∈ fst pw ⟩
```

<!--en-->
The next hypotheses supply the second membership, the table application, and the code-set description. Crucially, the relation premise ranges over every `r` recorded by the table at `δ`, because in the reading direction the existential formula may have bound any such `rl`; the final equation shown here fixes `ro` to the canonical code order.
<!--zh-->
接下来的假设给出第二条隶属、序表应用与码集描述。关键在于，关系前提遍历序表在 `δ` 处记录的每个 `r`，因为在读取方向，存在公式可能绑定其中任意一个 `rl`；这里最后显示的等式把 `ro` 固定为典范码序。
<!--ja-->
続く仮定は、第二の所属、順序表の適用、コード集合の記述を与える。特に、関係についての前提は、順序表が `δ` で記録するすべての `r` に及ぶ。読み出す向きでは、存在論理式がそのどの `rl` を束縛していてもよいからである。ここで最後に現れる等式は、`ro` を正準なコード順序に固定する。
<!--/-->

```agda
          → ⟨ fst (lookup v γ) ∈ fst pw ⟩
          → ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
          → ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
          → ((r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r)
          → fst ro ≡ fst codeOrder
```

<!--en-->
The outward argument has now reached the innermost condition. Once the six existential witnesses have been identified, `atAll` reads satisfaction of `StepAt` into the merely existing data of two least names and their name comparison. Mapping the next argument over that propositional truncation will turn the name comparison into the required host-side `Under` comparison without choosing names outside the truncation.
<!--zh-->
向外论证现在到达最内层条件。六个存在见证辨认完毕后，`atAll` 从 `StepAt` 的满足读出两条最小名字及其名字比较的仅仅存在。下一步在这项命题截断上作映射，把名字比较转成所需的宿主层 `Under` 比较，而不会从截断之外选出名字。
<!--ja-->
外向きの議論は、ここで最内側の条件に到達する。六つの存在証人を同定すると、`atAll` は `StepAt` の充足から、二つの最小の名前とその名前比較が単に存在することを読み出す。次の議論をこの命題的切り詰めの上で写すことで、切り詰めの外へ名前を選び出すことなく、名前比較を必要なホスト側の `Under` 比較へ変換する。
<!--/-->

```agda
          → fst c0 ≡ fst (AllCodes ∅ʟ)
          → StepHolds tw pw rl cs ro c0 → Goal
    atAll tw pw rl cs ro c0 hg hdef hu hv happ hcs vals qro qc0 hstep =
      map₁ atNames (K.holds-out hstep)
      where
```

<!--en-->
The tower identification equation says the tower bound in the formula equals the constructible stage at the argument ordinal, read out through the layer-adequacy lemma.
<!--zh-->
塔认同等式说公式中绑定的塔等于实参序数处的可构造层，由层充分性引理读取。
<!--ja-->
塔の同定の等式が、論理式で束縛された塔が、入力の順序数での構成可能な段階に等しいことを、層の妥当性の補題で読み出す。
<!--/-->

```agda
      qtw : fst tw ≡ Lset δ
      qtw = Lset-only zero (suc d) (tw ∷ γ) hg od
```

<!--en-->
The definable-subset identification says the bound set is the definable power set of the stage, transported along the tower equation.
<!--zh-->
可定义子集认同说被绑定的集合是该层的可定义幂集，沿塔等式运输。
<!--ja-->
定義可能な部分集合の同定が、束縛された集合がその段階の定義可能冪集合であることを、塔の等式に沿って述べる。
<!--/-->

```agda
      qpw : fst pw ≡ 𝒟ₒ (Lset δ)
      qpw = subst ⟨_⟩ (DefAt-stage δ od zero (suc zero) (pw ∷ tw ∷ γ) qtw) hdef
```

<!--en-->
Membership in the successor stage is recovered by two transports: the first identifies the definable power set with the successor stage via the successor identity of the constructible layer, and the second rewrites along the identification of the bound set with that definable power set. Together they place the compared object inside `Lset (sucV δ)`.
<!--zh-->
后继层隶属由两次运输恢复：第一次沿可构造层后继恒等式认同可定义幂集与后继层，第二次沿被绑定集合认同为该可定义幂集的等式改写。二者共同把被比较对象放进后继层 `Lset (sucV δ)` 中。
<!--ja-->
後続の段階への所属は、二度の輸送によって復元される。最初の輸送が、構成可能な層の後続の恒等式を使って、定義可能冪集合と後続の段階を同一視する。二つ目の輸送が、束縛された集合がその定義可能冪集合と等しいという等式に沿って書き換える。二つ合わせて、比較される対象を後続の段階 `Lset (sucV δ)` の中に置く。
<!--/-->

```agda
      inSuc : (x : V ℓ) → ⟨ x ∈ fst pw ⟩ → ⟨ x ∈ Lset (sucV δ) ⟩
      inSuc x h = subst (λ z → ⟨ x ∈ z ⟩) (sym (Lset-suc δ))
        (subst (λ z → ⟨ x ∈ z ⟩) qpw h)
```

<!--en-->
The first comparison candidate is the underlying set at slot `u`, presented as a member of the successor stage by the recovery lemma.
<!--zh-->
第一个比较候选是槽位 `u` 处的底层集合，经恢复引理呈现为后继段的成员。
<!--ja-->
最初の比較の候補は、枠 `u` の基礎の集合であり、復元の補題によって後続の段階の要素として提示される。
<!--/-->

```agda
      a : New δ
      a = fst (lookup u γ) , inSuc (fst (lookup u γ)) hu
```

<!--en-->
The second comparison candidate is the underlying set at slot `v`, similarly presented.
<!--zh-->
第二个比较候选是槽位 `v` 处的底层集合，同样呈现。
<!--ja-->
二つ目の比較の候補は、枠 `v` の基礎の集合で、同様に提示される。
<!--/-->

```agda
      b : New δ
      b = fst (lookup v γ) , inSuc (fst (lookup v γ)) hv
```

<!--en-->
Satisfaction of the application formula says that `rl` is a value recorded by the table at `δ`. The outward hypothesis `vals` deliberately applies to every such recorded value, so it supplies `IsRel δ rl` for the particular witness chosen inside `Stp`. This is a soundness condition on all possible table witnesses, not a uniqueness claim about the table value.
<!--zh-->
应用公式的满足说明 `rl` 是表在 `δ` 处记录的一个取值。向外假设 `vals` 特意覆盖每个这样的记录值，所以也为 `Stp` 内部选出的这个见证提供 `IsRel δ rl`。这是对所有可能表见证的可靠性条件，并非表取值的唯一性断言。
<!--ja-->
適用論理式の充足は、`rl` が表の `δ` に記録された値であることを述べる。外向きの仮定 `vals` は、そのように記録されたすべての値を意図的に対象とするため、`Stp` の内部で選ばれたこの証人についても `IsRel δ rl` を与える。これは可能な表の証人すべてに対する健全性の条件であり、表の値の一意性を主張するものではない。
<!--/-->

```agda
      hrel : IsRel δ rl
      hrel = vals rl
        (subst ⟨_⟩ (appAt-adequate (sh3 f) (sh3 d) zero (rl ∷ pw ∷ tw ∷ γ)) happ)
```

<!--en-->
The outward reading of the code-set description identifies `cs` with `AllCodes (LsetS δ od)`{.Agda}, the code set over the current stage `Lset δ`{.Agda}. The compared objects live in the successor stage, but their names are formed relative to the preceding stage, so this code set is indexed by `δ`, not by `sucV δ`{.Agda}.
<!--zh-->
码集描述的向外读式把 `cs` 认同为 `AllCodes (LsetS δ od)`{.Agda}，即当前层 `Lset δ`{.Agda} 上的码集。被比较对象属于后继层，但其名字相对于前一层形成，所以这里的码集以 `δ` 为指标，而不是以 `sucV δ`{.Agda} 为指标。
<!--ja-->
符号集合の記述を外向きに読むと、`cs` は `AllCodes (LsetS δ od)`{.Agda}、すなわち現在の段階 `Lset δ`{.Agda} 上の符号集合と同一視される。比較される対象は後続段階に属するが、その名前は直前の段階に関して作られるので、ここでの符号集合は `sucV δ`{.Agda} ではなく `δ` で添字づけられる。
<!--/-->

```agda
      qcs : fst cs ≡ fst (AllCodes (LsetS δ od))
      qcs = cong fst (CodesAt-out (LsetS δ od) zero (sh3 zero)
              (cs ∷ rl ∷ pw ∷ tw ∷ γ) qtw hcs)
```

<!--en-->
With the tower, stage relation, code set, and two fixed code objects now identified, `Slots` connects the six witnesses to the previously proved adequacy theorem for name comparison. This shared instance lets the remaining argument speak interchangeably about the innermost formula and the corresponding least-name data.
<!--zh-->
塔、层关系、码集以及两个固定码对象现在都已辨认，`Slots` 因而把六个见证接到先前证明的名字比较充分性定理上。借助这一共同实例，余下论证可以在最内层公式与相应最小名字资料之间往返。
<!--ja-->
塔、段階関係、符号集合、二つの固定された符号対象がすべて同定されたので、`Slots` は六つの証人を、すでに証明された名前比較の妥当性定理へ接続する。この共通の具体化により、残りの議論では最内側の論理式と対応する最小名のデータを相互に読み替えられる。
<!--/-->

```agda
      module K = Slots tw pw rl cs ro c0 qtw hrel qcs qro qc0
```

<!--en-->
Inside the propositional truncation returned by the name adequacy theorem, suppose `t₁` and `t₂` are least names for the two compared sets and `t₁ ≺ₙ t₂`. The target `Under` contains more than the final comparison: it also records that both sets belong to `Lset (sucV δ)`. Those two membership components have already been established by `a` and `b`.
<!--zh-->
在名字充分性定理返回的命题截断内部，设 `t₁`、`t₂` 分别是两个被比较集合的最小名字，且 `t₁ ≺ₙ t₂`。目标 `Under` 不只含最终比较，还记录两个集合都属于 `Lset (sucV δ)`；这两项隶属已经由 `a` 与 `b` 建立。
<!--ja-->
名前の妥当性定理が返す命題的切り詰めの内部で、`t₁` と `t₂` を比較される二つの集合の最小名とし、`t₁ ≺ₙ t₂` とする。目標の `Under` は最後の比較だけでなく、二つの集合がともに `Lset (sucV δ)` に属することも記録する。この二つの所属成分は、すでに `a` と `b` によって得られている。
<!--/-->

```agda
      atNames : Σ[ t₁ ∶ NM.Name ] Σ[ t₂ ∶ NM.Name ]
                  ( K.LeastFst t₁ × ( K.LeastSnd t₂ × NM._≺ₙ_ t₁ t₂ ) )
              → Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ))
      atNames (t₁ , (t₂ , (l₁ , (l₂ , lt)))) =
          a .snd
```

<!--en-->
The two outward least-name readings translate the local predicates back to `IsLeastName`. The theorem `stepAt-fill` then says that comparison of these least names entails the relation of `stepOrder δ od` between the represented new elements. Together with the memberships from the preceding group, this completes `Under`.
<!--zh-->
两条最小名字的向外读式把局部谓词还原为 `IsLeastName`。随后 `stepAt-fill` 说明，这两条最小名字之间的比较蕴含其所表示新元素之间的 `stepOrder δ od` 关系。再合并上一组的两项隶属，即得到完整的 `Under`。
<!--ja-->
二つの最小名についての外向きの読みは、局所的な述語を `IsLeastName` へ戻す。続いて `stepAt-fill` は、これらの最小名の比較から、それらが表す新しい要素の間の `stepOrder δ od` 関係が従うことを示す。直前に得た二つの所属と合わせて、`Under` が完成する。
<!--/-->

```agda
        , ( b .snd
          , stepAt-fill δ ordW a b t₁ t₂
              (K.leastFst-out t₁ l₁) (K.leastSnd-out t₂ l₂) lt )
```

<!--en-->
## Packing
<!--zh-->
## 装回
<!--ja-->
## 束縛を組み立てる
<!--/-->

<!--en-->
For the converse direction, fix one actual table value `rl`, evidence that the table records it at `δ`, and evidence that it represents the required stage relation. Also fix the two successor-stage memberships carried by an `Under` comparison. Unlike the outward direction, this construction has a particular local table value available and can use it as the third existential witness of `Stp`.
<!--zh-->
反向论证固定一个实际表取值 `rl`，以及表在 `δ` 处记录它和它表示所需层关系的证据；同时固定一项 `Under` 比较携带的两条后继层隶属。与向外方向不同，这个构造手中已有一个具体的局部表取值，可以把它用作 `Stp` 的第三个存在见证。
<!--ja-->
逆向きの議論では、実際の表の値 `rl` と、それが表の `δ` に記録され、必要な段階関係を表すことの証拠を固定する。さらに、`Under` 比較が含む二つの後続段階への所属も固定する。外向きの場合と異なり、この構成では具体的な局所表の値が手元にあるため、それを `Stp` の三番目の存在証人として使える。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module Pack (rl : S) (hpr : ⟨ pr δ (fst rl) ∈ fst (lookup f γ) ⟩)
              (hrel : IsRel δ rl)
              (hx : ⟨ fst (lookup u γ) ∈ Lset (sucV δ) ⟩)
              (hy : ⟨ fst (lookup v γ) ∈ Lset (sucV δ) ⟩)
              where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The packing argument uses the six witnesses in the order prescribed by `Stp`{.Agda}: `towerS δ od`{.Agda}, `powS δ od`{.Agda}, the supplied table value `rl`, `AllCodes (LsetS δ od)`{.Agda}, `codeOrder`{.Agda}, and `AllCodes ∅ʟ`{.Agda}. In particular, the fourth witness is the code set over the current stage `Lset δ`{.Agda}; only the two objects being compared belong to its successor stage.
<!--zh-->
装回论证按 `Stp`{.Agda} 规定的次序使用六个见证：`towerS δ od`{.Agda}、`powS δ od`{.Agda}、给定的表取值 `rl`、`AllCodes (LsetS δ od)`{.Agda}、`codeOrder`{.Agda} 与 `AllCodes ∅ʟ`{.Agda}。特别地，第四个见证是当前层 `Lset δ`{.Agda} 上的码集；只有被比较的两个对象属于其后继层。
<!--ja-->
組み立てる議論では、`Stp`{.Agda} が定める順序で六つの証人を使う。すなわち `towerS δ od`{.Agda}、`powS δ od`{.Agda}、与えられた表の値 `rl`、`AllCodes (LsetS δ od)`{.Agda}、`codeOrder`{.Agda}、`AllCodes ∅ʟ`{.Agda} である。特に第四の証人は現在の段階 `Lset δ`{.Agda} 上の符号集合であり、その後続段階に属するのは比較される二つの対象である。
<!--/-->

```agda
    private module K = Slots (towerS δ od) (powS δ od) rl (AllCodes (LsetS δ od))
                         codeOrder (AllCodes ∅ʟ) (towerS-fst δ od) hrel refl refl refl
```

<!--en-->
The first comparison candidate is presented by its membership in the successor stage.
<!--zh-->
第一个比较候选由其在后继段中的隶属呈现。
<!--ja-->
最初の比較の候補は、後続の段階での所属によって提示される。
<!--/-->

```agda
    private
      a : New δ
      a = fst (lookup u γ) , hx
```

<!--en-->
The second comparison candidate is similarly presented.
<!--zh-->
第二个比较候选同样呈现。
<!--ja-->
二つ目の比較の候補も同じように提示される。
<!--/-->

```agda
      b : New δ
      b = fst (lookup v γ) , hy
```

<!--en-->
Every new element has a least name relative to the fixed host-side well-order `ordW`, so the first candidate supplies a pair consisting of a name and its `IsLeastName` proof. This is an explicit local witness used to fill the formula; it does not assert that `Stp` uniquely determines a name.
<!--zh-->
相对于固定的宿主层良序 `ordW`，每个新元素都有最小名字，因此第一个候选给出一条名字及其 `IsLeastName` 证明所成的对。这是填入公式时使用的显式局部见证，并不声称 `Stp` 唯一确定某条名字。
<!--ja-->
固定されたホスト側の整列順序 `ordW` に関して、各新要素には最小名があるので、最初の候補から名前とその `IsLeastName` の証明の組が得られる。これは論理式を満たすための明示的で局所的な証人であり、`Stp` が名前を一意に定めると主張するものではない。
<!--/-->

```agda
      n₁ : Σ[ t ∶ NM.Name ] IsLeastName δ ordW t (fst (lookup u γ))
      n₁ = leastNameOf δ ordW a
```

<!--en-->
The same theorem supplies a least name for the second candidate. These two locally chosen names are compared and then passed to the inward adequacy theorem for `StepAt`{.Agda}. Its existential semantics, followed by the six outer existential binders of `Stp`{.Agda}, hides the names again; this construction exports no chosen pair of names.
<!--zh-->
同一条定理为第二个候选提供一条最小名字。论证在局部比较这两条选出的名字，再把它们交给 `StepAt`{.Agda} 的向内充分性定理。该公式的存在语义以及 `Stp`{.Agda} 外围的六个存在绑定随后重新隐藏这些名字；此构造不会导出一对已选名字。
<!--ja-->
同じ定理から、二つ目の候補についても最小名が得られる。局所的に選んだ二つの名前を比較し、`StepAt`{.Agda} の内向きの妥当性定理へ渡す。その論理式の存在の意味論と、それを囲む `Stp`{.Agda} の六つの存在束縛子によって、名前は再び隠される。この構成が選ばれた名前の組を外へ出すことはない。
<!--/-->

```agda
      n₂ : Σ[ t ∶ NM.Name ] IsLeastName δ ordW t (fst (lookup v γ))
      n₂ = leastNameOf δ ordW b
```

<!--en-->
The first witness is `towerS δ od`{.Agda}. Its defining theorem proves that it satisfies `LsetGraphAt`{.Agda} in the extended environment and therefore has underlying set `Lset δ`{.Agda}, as required by the first binder.
<!--zh-->
第一个见证取 `towerS δ od`{.Agda}。其定义定理证明它在扩展环境中满足 `LsetGraphAt`{.Agda}，因而底层集合是第一个绑定所要求的 `Lset δ`{.Agda}。
<!--ja-->
最初の証人には `towerS δ od`{.Agda} を取る。その定義定理は、これが拡張された環境で `LsetGraphAt`{.Agda} を満たし、したがって第一の束縛子が要求する `Lset δ`{.Agda} を基礎集合にもつことを示す。
<!--/-->

```agda
      hg : ⟨ (towerS δ od ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
      hg = Lset-defines zero (suc d) (towerS δ od ∷ γ) od (towerS-fst δ od)
```

<!--en-->
The second witness is `powS δ od`{.Agda}, whose underlying set is the definable-subset set `𝒟ₒ (Lset δ)`{.Agda}. The equation supplied by `DefAt-stage`{.Agda} characterizes satisfaction of `DefAt`{.Agda}; transporting `powS-fst`{.Agda} across that characterization proves the required satisfaction statement. This is the definable-subset set of the stage, not its full power set.
<!--zh-->
第二个见证取 `powS δ od`{.Agda}，其底层集合是可定义子集集 `𝒟ₒ (Lset δ)`{.Agda}。`DefAt-stage`{.Agda} 给出的等式刻画 `DefAt`{.Agda} 的满足；沿这一刻画运输 `powS-fst`{.Agda}，便得到所需的满足陈述。这里使用的是该层的可定义子集集，而不是它的完整幂集。
<!--ja-->
二つ目の証人は `powS δ od`{.Agda} であり、その基礎集合は定義可能部分集合の集合 `𝒟ₒ (Lset δ)`{.Agda} である。`DefAt-stage`{.Agda} が与える等式は `DefAt`{.Agda} の充足を特徴づける。この特徴づけに沿って `powS-fst`{.Agda} を輸送すると、必要な充足の主張が得られる。ここで使うのはこの段階の定義可能部分集合の集合であり、完全な冪集合ではない。
<!--/-->

```agda
      hdef : ⟨ (powS δ od ∷ towerS δ od ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      hdef = subst ⟨_⟩
        (sym (DefAt-stage δ od zero (suc zero)
                (powS δ od ∷ towerS δ od ∷ γ) (towerS-fst δ od)))
        (powS-fst δ od)
```

<!--en-->
To fill the two membership conjuncts of `Stp`, the direction needed here is from the successor stage into the chosen definable-subset object. The identity `Lset-suc δ` rewrites membership in `Lset (sucV δ)` as membership in `𝒟ₒ (Lset δ)`, and `powS-fst` then rewrites that set as the underlying set of `powS δ od`.
<!--zh-->
为了填入 `Stp` 的两项隶属合取，这里需要的方向是从后继层进入选定的可定义子集对象。恒等式 `Lset-suc δ` 把 `Lset (sucV δ)` 中的隶属改写为 `𝒟ₒ (Lset δ)` 中的隶属，`powS-fst` 再把后者改写为 `powS δ od` 的底层集合。
<!--ja-->
`Stp` の二つの所属の連言を満たすため、ここで必要なのは後続段階から選ばれた定義可能部分集合の対象へ向かう向きである。等式 `Lset-suc δ` により、`Lset (sucV δ)` への所属を `𝒟ₒ (Lset δ)` への所属へ書き換え、さらに `powS-fst` により、それを `powS δ od` の基礎となる集合への所属へ書き換える。
<!--/-->

```agda
      inPow : (x : V ℓ) → ⟨ x ∈ Lset (sucV δ) ⟩ → ⟨ x ∈ fst (powS δ od) ⟩
      inPow x h = subst (λ z → ⟨ x ∈ z ⟩) (sym (powS-fst δ od))
        (subst (λ z → ⟨ x ∈ z ⟩) (Lset-suc δ) h)
```

<!--en-->
The application satisfaction is transported from the table-entry proof along the adequacy of the application coding.
<!--zh-->
应用满足由表条目证明沿应用编码的充分性运输。
<!--ja-->
適用の充足は、表の項目の証明から、適用の符号化の妥当性に沿って運ばれる。
<!--/-->

```agda
      happ : ⟨ (rl ∷ powS δ od ∷ towerS δ od ∷ γ)
              ⊨ appAt (sh3 f) (sh3 d) zero ⟩
      happ = subst ⟨_⟩
        (sym (appAt-adequate (sh3 f) (sh3 d) zero
                (rl ∷ powS δ od ∷ towerS δ od ∷ γ))) hpr
```

<!--en-->
For the fourth witness, the inward reading of `CodesAt`{.Agda} proves that `AllCodes (LsetS δ od)`{.Agda} satisfies the code-set description over the tower `Lset δ`{.Agda}. No code set at the successor stage is needed.
<!--zh-->
对第四个见证，`CodesAt`{.Agda} 的向内读式证明 `AllCodes (LsetS δ od)`{.Agda} 满足塔 `Lset δ`{.Agda} 上的码集描述。这里不需要后继层上的码集。
<!--ja-->
第四の証人について、`CodesAt`{.Agda} の内向きの読みは、`AllCodes (LsetS δ od)`{.Agda} が塔 `Lset δ`{.Agda} 上の符号集合の記述を満たすことを示す。後続段階上の符号集合は必要ない。
<!--/-->

```agda
      hcs : ⟨ (AllCodes (LsetS δ od) ∷ rl ∷ powS δ od ∷ towerS δ od ∷ γ)
             ⊨ CodesAt zero (sh3 zero) ⟩
      hcs = CodesAt-in (LsetS δ od) zero (sh3 zero)
        (AllCodes (LsetS δ od) ∷ rl ∷ powS δ od ∷ towerS δ od ∷ γ)
        (towerS-fst δ od) refl
```

<!--en-->
Assume the host-side `stepOrder` comparison. The two least names already chosen satisfy the local least-name predicates after the inward equality adjustments. It remains only to turn the host comparison into the name comparison required by the innermost `StepAt` formula.
<!--zh-->
现假设宿主层的 `stepOrder` 比较成立。经向内的等式方向调整，先前选出的两条最小名字满足局部最小名字谓词；余下只需把宿主比较转成最内层 `StepAt` 公式所需的名字比较。
<!--ja-->
ホスト側の `stepOrder` 比較を仮定する。すでに選んだ二つの最小名は、内向きの等式の向きを調整すると、局所的な最小名述語を満たす。残るのは、ホスト側の比較を最内側の `StepAt` 論理式が要求する名前比較へ変換することだけである。
<!--/-->

```agda
      hstep : relOf (stepOrder δ od) a b
            → StepHolds (towerS δ od) (powS δ od) rl (AllCodes (LsetS δ od))
                codeOrder (AllCodes ∅ʟ)
      hstep cmp = K.holds-in (n₁ .fst) (n₂ .fst)
        (K.leastFst-in (n₁ .fst) (n₁ .snd)) (K.leastSnd-in (n₂ .fst) (n₂ .snd))
```

<!--en-->
The theorem `stepAt-read` performs exactly that conversion, using the leastness proofs for `n₁` and `n₂`. Feeding the resulting name comparison to `holds-in` proves the innermost satisfaction statement. The argument uses the already existing host-side `stepOrder`; it does not construct a new well-order.
<!--zh-->
定理 `stepAt-read` 正好完成这一转换，并使用 `n₁` 与 `n₂` 的最小性证明。把所得名字比较交给 `holds-in`，便证明最内层满足陈述。论证使用已经存在的宿主层 `stepOrder`，并未构造新的良序。
<!--ja-->
定理 `stepAt-read` は、`n₁` と `n₂` の最小性の証明を使って、ちょうどこの変換を行う。得られた名前比較を `holds-in` に渡すと、最内側の充足が証明される。この議論は既存のホスト側の `stepOrder` を用いるのであり、新しい整列順序を構成するものではない。
<!--/-->

```agda
        (stepAt-read δ ordW a b (n₁ .fst) (n₂ .fst) (n₁ .snd) (n₂ .snd) cmp)
```

<!--en-->
The six object-language existentials are interpreted as six nested propositionally truncated dependent pairs. `packAll`{.Agda} starts the nesting with `towerS δ od`{.Agda} and its `LsetGraphAt`{.Agda} proof. Although this proof constructs a concrete witness locally, the outermost existential boundary immediately retains only its propositional truncation.
<!--zh-->
对象语言的六个存在量词被解释为六层嵌套的命题截断依值对。`packAll`{.Agda} 先装入 `towerS δ od`{.Agda} 及其 `LsetGraphAt`{.Agda} 证明。尽管证明在局部构造了具体见证，最外层存在边界立即只保留它的命题截断。
<!--ja-->
対象言語の六つの存在量化は、依存対の命題的切り詰めが六重に入れ子になったものとして解釈される。`packAll`{.Agda} は `towerS δ od`{.Agda} とその `LsetGraphAt`{.Agda} の証明から、この入れ子を組み始める。証明の内部では具体的な証人を構成するが、最も外側の存在の境界では、その命題的切り詰めだけが直ちに残る。
<!--/-->

```agda
    packAll : relOf (stepOrder δ od) a b → ∥ (Σ[ tw ∶ S ] One tw) ∥₁
    packAll cmp =
      ∣ towerS δ od
      , ( hg
        , ∣ powS δ od
```

<!--en-->
The second witness is `powS δ od`{.Agda}, accompanied by its `DefAt`{.Agda} satisfaction and by the two memberships transported from the successor stage. The third witness is the supplied table value `rl`; its recorded-pair proof yields the required satisfaction of `appAt`{.Agda}. Thus the filling direction uses a particular relation value already provided by the caller rather than choosing one from the table.
<!--zh-->
第二个见证是 `powS δ od`{.Agda}，并附有它对 `DefAt`{.Agda} 的满足，以及从后继层运输来的两条隶属。第三个见证是给定的表取值 `rl`；它的有序对成员证明给出所需的 `appAt`{.Agda} 满足。因此，填充方向使用调用方已经给出的特定关系值，而不是从表中选取一个值。
<!--ja-->
第二の証人は `powS δ od`{.Agda} であり、`DefAt`{.Agda} の充足と、後続段階から輸送した二つの所属が付随する。第三の証人は与えられた表の値 `rl` であり、その順序対の所属証明から必要な `appAt`{.Agda} の充足が得られる。したがって、埋める向きでは、表から値を選ぶのではなく、呼び出し側がすでに与えた特定の関係値を使う。
<!--/-->

```agda
          , ( hdef
            , ( inPow (fst (lookup u γ)) hx
              , ( inPow (fst (lookup v γ)) hy
                , ∣ rl
                  , ( happ
```

<!--en-->
The code set satisfaction is followed by the code-order element and its identification equation, then by the empty-alphabet code set.
<!--zh-->
码集满足之后是码序元素及其认同等式，再后是空字母表码集。
<!--ja-->
符号の集合の充足のあとに、符号の順序の要素とその同定の等式が続き、さらに空のアルファベットの符号の集合が続く。
<!--/-->

```agda
                    , ∣ AllCodes (LsetS δ od)
                      , ( hcs
                        , ∣ codeOrder
                          , ( refl
                            , ∣ AllCodes ∅ʟ
```

<!--en-->
The final wrappers insert the empty-alphabet code set, its identifying equality, and the satisfaction of the innermost step formula. Closing all six truncations proves `Stp` while exposing none of the chosen tower, relation, code, or name witnesses to later users.
<!--zh-->
最后几层包装装入空字母表码集、辨认它的等式以及最内层步进公式的满足。封闭全部六层截断后即证明 `Stp`，同时不会向后续使用者暴露所选的塔、关系、码或名字见证。
<!--ja-->
最後の包み込みでは、空のアルファベットの符号集合、それを同定する等式、最内側のステップ論理式の充足を挿入する。六つの切り詰めをすべて閉じることで `Stp` が証明されるが、選んだ塔、関係、符号、名前の証人は後の利用者へ公開されない。
<!--/-->

```agda
                              , ( refl , hstep cmp ) ∣₁ ) ∣₁ ) ∣₁ ) ∣₁ ) ) ) ∣₁ ) ∣₁
```
</div>
</details>

<!--en-->
## The two readings
<!--zh-->
## 两条读式
<!--ja-->
## 二つの読み
<!--/-->

<!--en-->
The two readings now give the exact interface required by the recursive table, and their types record the essential asymmetry. The outward direction must accept every relation value recorded at the stage and returns only `∥ Under ... ∥₁`{.Agda}. The inward direction receives one specified recorded value with its `IsRel`{.Agda} proof and an untruncated `Under`{.Agda} comparison, from which it constructs satisfaction of `Stp`{.Agda}.
<!--zh-->
两条读式现在给出递归序表所需的精确接口，而其类型记录了关键的不对称性。向外方向必须接受该层所记录的每个关系值，并且只返回 `∥ Under ... ∥₁`{.Agda}。向内方向则接收一个指定的已记录取值及其 `IsRel`{.Agda} 证明，再接收一项未经截断的 `Under`{.Agda} 比较，由此构造 `Stp`{.Agda} 的满足。
<!--ja-->
二つの読みは、再帰的な表が必要とする正確なインターフェースを与え、その型が本質的な非対称性を記録する。外向きは、その段階で記録されたすべての関係値を扱わなければならず、返すのは `∥ Under ... ∥₁`{.Agda} だけである。内向きは、指定された一つの記録済みの値とその `IsRel`{.Agda} の証明、さらに切り詰められていない `Under`{.Agda} の比較を受け取り、そこから `Stp`{.Agda} の充足を構成する。
<!--/-->

```agda
  opaque
    unfolding Stp StepHolds
```

<!--en-->
For the outward reading, assume every value recorded by the table at `δ` represents the required stage relation. Satisfaction of `Stp` supplies only propositionally truncated existential witnesses, so `read` eliminates the six truncations one at a time into `Goal`, which is itself propositionally truncated.
<!--zh-->
向外读取时，假设表在 `δ` 处记录的每个取值都表示所需层关系。`Stp` 的满足只给出命题截断下的存在见证，因此 `read` 逐层消去六项截断，目标则是本身经过命题截断的 `Goal`。
<!--ja-->
外向きの読みでは、表の `δ` に記録されたすべての値が必要な段階関係を表すと仮定する。`Stp` の充足が与える存在証人は命題的に切り詰められているため、`read` は六つの切り詰めを一つずつ、同じく命題的に切り詰められた `Goal` へ除去する。
<!--/-->

```agda
    read : ((r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r)
         → ⟨ γ ⊨ Stp d f u v ⟩ → Goal
    read vals = rec₁ squash₁
      (λ { (tw , (hg , hpw)) → rec₁ squash₁
        (λ { (pw , (hdef , (hu , (hv , hrl)))) → rec₁ squash₁
```

<!--en-->
The eliminations follow the binder order: tower, definable-subset set, table value, code set, code order, and empty-alphabet code set. At each level the witness remains available only inside the continuation for the next truncation; the construction never returns a selected six-tuple.
<!--zh-->
消去遵循绑定次序：塔、可定义子集集、表取值、码集、码序以及空字母表码集。每一层的见证只在下一层截断的续体内部可用；整个构造从不返回一个选定的六元组。
<!--ja-->
除去は束縛子の順、すなわち塔、定義可能部分集合の集合、表の値、符号集合、符号順序、空のアルファベットの符号集合の順に進む。各段階の証人は次の切り詰めを扱う継続の内部でだけ利用でき、選択された六つ組が返されることはない。
<!--/-->

```agda
          (λ { (rl , (happ , hcs)) → rec₁ squash₁
            (λ { (cs , (hcs , hro)) → rec₁ squash₁
              (λ { (ro , (qro , hc0)) → rec₁ squash₁
                (λ { (c0 , (qc0 , hstep)) →
                  atAll tw pw rl cs ro c0 hg hdef hu hv happ hcs vals qro qc0 hstep })
```

<!--en-->
Once all six witnesses and their conditions are locally available, `atAll` produces the propositionally truncated `Under` comparison. The nested eliminators then close in the reverse syntactic order, preserving the truncation boundary required by the object-language existentials.
<!--zh-->
六个见证及其条件在局部全部可用后，`atAll` 产出命题截断的 `Under` 比较。嵌套消去器随后按相反的语法次序闭合，从而保留对象语言存在量词所要求的截断边界。
<!--ja-->
六つの証人とその条件が局所的にすべて揃うと、`atAll` は命題的に切り詰められた `Under` 比較を返す。その後、入れ子の除去子が構文とは逆の順で閉じられ、対象言語の存在量化が要求する切り詰めの境界が保たれる。
<!--/-->

```agda
                hc0 }) hro }) hcs }) hrl }) hpw })
```

<!--en-->
The inward reading consumes a specific table value with its membership and relation proof, together with the two membership proofs and the host-side comparison, and packs everything into the six-layer existential.
<!--zh-->
向内读法消耗特定表取值连同其隶属与关系证明，连同两条隶属证明与宿主侧比较，并把一切打包进六层存在量词。
<!--ja-->
内向きの読み出しは、特定の表の値と、その所属と関係の証明と、二つの所属の証明とホスト側の比較を消費して、すべてを六重の存在量化の中にまとめる。
<!--/-->

```agda
    fill : (r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r
         → Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ))
         → ⟨ γ ⊨ Stp d f u v ⟩
    fill r hpr hrel (hx , (hy , cmp)) = Pack.packAll r hpr hrel hx hy cmp
```
</div>
</details>

<!--en-->
The outward reading of the step formula is exported as the first adequacy direction: satisfaction implies a truncated step comparison.
<!--zh-->
步进公式的向外读法作为第一条充分性方向导出：满足蕴含截断的步进比较。
<!--ja-->
ステップの論理式の外向きの読み出しが、最初の妥当性の方向として書き出される。充足が、切り詰められたステップの比較を含意する、というものである。
<!--/-->

```agda
stp-out : StpOut Stp
stp-out = Reading.read
```

<!--en-->
## The frame opened
<!--zh-->
## 框架被打开
<!--ja-->
## フレームを具体化する
<!--/-->

<!--en-->
The inward reading of the step formula is exported as the second adequacy direction: a specific table entry with the correct relation and a host-side comparison together imply the formula satisfaction.
<!--zh-->
步进公式的向内读法作为第二条充分性方向导出：特定表条目连同正确关系与宿主侧比较共同蕴含公式满足。
<!--ja-->
ステップの論理式の内向きの読み出しが、二つ目の妥当性の方向として書き出される。正しい関係をもつ特定の表の値とホスト側の比較が合わせて、論理式の充足を含意する、というものである。
<!--/-->

```agda
stp-in : StpIn Stp
stp-in = Reading.fill
```

<!--en-->
Supplying `Stp` and these two readings completes the abstract construction of the stage-order table. In particular, it yields for every ordinal stage an internal set `relL` together with `relL-fill` and `relL-rep`, which convert pairwise between the host relation of `orderAt` and membership of the corresponding ordered pair in `relL`. This is a representation of the relation graph; no object-language assertion that `relL` satisfies a well-order formula is proved here.
<!--zh-->
把 `Stp` 及其两条读式交给抽象构造，层序表便完整实例化。特别地，对每个序数层都会得到一个内部集合 `relL`，以及 `relL-fill` 与 `relL-rep`；二者逐对在 `orderAt` 的宿主关系和相应有序对属于 `relL` 之间转换。这里得到的是关系图的表示，并未证明一条对象语言陈述，声称 `relL` 满足某个良序公式。
<!--ja-->
`Stp` とこの二つの読みを抽象的な構成へ与えることで、段階順序の表が完全に具体化される。とくに各順序数段階について内部集合 `relL` と `relL-fill`、`relL-rep` が得られ、`orderAt` のホスト側の関係と、対応する順序対が `relL` に属することを要素ごとに相互変換できる。ここで得られるのは関係グラフの表現であり、`relL` が整列順序の論理式を満たすという対象言語の主張は証明されていない。
<!--/-->

```agda
open Ordered Stp stp-out stp-in public
```

<!--en-->
## The order at the bounding ordinal
<!--zh-->
## 上界序数处的序
<!--ja-->
## 上界順序数における順序
<!--/-->

<!--en-->
For a constructible set `a`, `stageBound`{.Agda} chooses an ordinal above both `ω` and the first stage at which `a` appears. Consequently `Lset boundOrd`{.Agda} is high enough to contain the members of `a` and the members of those members, which is the local domain needed by the later transversal argument. The chosen bound is sufficient for that use; it is not asserted to be the least or a uniquely determined bound for `a`.
<!--zh-->
对可构造集合 `a`，`stageBound`{.Agda} 选取一个同时高于 `ω` 与 `a` 首次出现之层的序数。因此，`Lset boundOrd`{.Agda} 足以容纳 `a` 的成员以及这些成员的成员，这正是后续横截论证所需的局部论域。所选界足以完成这项工作；本章不声称它是 `a` 的最小界或唯一确定的界。
<!--ja-->
構成可能集合 `a` に対し、`stageBound`{.Agda} は `ω` と `a` が最初に現れる段階の両方より上にある順序数を選ぶ。したがって `Lset boundOrd`{.Agda} は、`a` の要素と、さらにそれらの要素を含むのに十分高く、後の横断集合の議論に必要な局所的な論域となる。選ばれた上界はこの目的には十分であるが、`a` に対する最小の上界または一意に定まる上界だとは主張しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Bound (a : V ℓ) (p : ⟨ isL a ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
  boundOrd : V ℓ
  boundOrd = stageBound a p .fst
```

<!--en-->
The same bounding result also certifies that `boundOrd` is an ordinal. This proof is what permits the already constructed host-side family `orderAt` to be specialized to the stage `Lset boundOrd`.
<!--zh-->
同一项界结果还证明 `boundOrd` 是序数。凭这项证明，先前已经构造的宿主层良序族 `orderAt` 才能专用于层 `Lset boundOrd`。
<!--ja-->
同じ上界の結果は、`boundOrd` が順序数であることも証明する。この証明により、すでに構成されているホスト側の族 `orderAt` を段階 `Lset boundOrd` に特殊化できる。
<!--/-->

```agda
  boundOrd-ord : IsOrd boundOrd
  boundOrd-ord = stageBound a p .snd .fst
```

<!--en-->
To obtain an internal relation object at this index, the table construction also needs the index itself to be constructible. An ordinal belongs to its own successor stage, so `boundOrd ∈ Lset (sucV boundOrd)` gives precisely the witness from which `Lset→isL` proves `isL boundOrd`.
<!--zh-->
为了在这个指标处取得内部关系对象，序表构造还需要指标本身可构造。序数属于它自身的后继层，因此 `boundOrd ∈ Lset (sucV boundOrd)` 正好给出见证，使 `Lset→isL` 能证明 `isL boundOrd`。
<!--ja-->
この添字で内部の関係対象を得るには、表の構成は添字自身が構成可能であることも必要とする。順序数は自分自身の後続段階に属するので、`boundOrd ∈ Lset (sucV boundOrd)` が、`Lset→isL` によって `isL boundOrd` を示すための証人になる。
<!--/-->

```agda
  boundOrd-isL : ⟨ isL boundOrd ⟩
  boundOrd-isL = Lset→isL (sucV boundOrd) (suc-ord boundOrd-ord) boundOrd
    (ord∈Lset-suc boundOrd boundOrd-ord)
```

<!--en-->
The relation to be represented is the pre-existing host-side strict well-order `orderAt boundOrd boundOrd-ord` on `Mem (Lset boundOrd)`. Its well-order structure belongs to this `SWO` value; the following lines only realize its binary relation as a set inside `L`.
<!--zh-->
待表示的关系是已经存在的宿主层严格良序 `orderAt boundOrd boundOrd-ord`，其载体为 `Mem (Lset boundOrd)`。良序结构由这个 `SWO` 值携带；以下各行只把它的二元关系实现为 `L` 内的集合。
<!--ja-->
表現する関係は、すでに存在するホスト側の狭義整列順序 `orderAt boundOrd boundOrd-ord` であり、その台は `Mem (Lset boundOrd)` である。整列順序の構造はこの `SWO` 値が持っており、以下の行はその二項関係を `L` の内部の集合として実現するだけである。
<!--/-->

```agda
  boundOrder : SWO (Mem (Lset boundOrd))
  boundOrder = orderAt boundOrd boundOrd-ord
```

<!--en-->
The table supplies that internal set as `relL` at the chosen ordinal. Thus `orderL` is an element of the model whose members are intended to be ordered pairs from the relation graph. It is not a new well-order construction and is not itself accompanied here by an internal satisfaction proof of the well-order axioms.
<!--zh-->
序表在所选序数处给出这个内部集合 `relL`。因此 `orderL` 是模型中的一个元素，其成员用来表示关系图中的有序对。它不是一项新的良序构造，本章也没有为它附上一份对象理论内部对良序公理的满足证明。
<!--ja-->
表は、選ばれた順序数におけるこの内部集合を `relL` として与える。したがって `orderL` はモデルの要素であり、その要素は関係グラフの順序対を表す。これは新しい整列順序の構成ではなく、整列順序の公理を対象理論の内部で満たすという証明も、ここでは付与されない。
<!--/-->

```agda
  orderL : S
  orderL = relL boundOrd boundOrd-isL boundOrd-ord
```

<!--en-->
The forward representation lemma takes a host-side comparison `relOf boundOrder x y` and inserts the encoded ordered pair `pr (fst x) (fst y)` into `orderL`. It establishes one direction of the pairwise correspondence between the existing `SWO` relation and its internal graph.
<!--zh-->
正向表示引理从宿主层比较 `relOf boundOrder x y` 出发，把编码有序对 `pr (fst x) (fst y)` 放入 `orderL`。这建立已有 `SWO` 关系与其内部关系图之间逐对对应的一个方向。
<!--ja-->
順方向の表現補題は、ホスト側の比較 `relOf boundOrder x y` から、符号化された順序対 `pr (fst x) (fst y)` を `orderL` に入れる。これにより、既存の `SWO` の関係とその内部グラフとの要素ごとの対応の一方向が得られる。
<!--/-->

```agda
  orderL-fill : (x y : Mem (Lset boundOrd)) → relOf boundOrder x y
              → ⟨ pr (fst x) (fst y) ∈ fst orderL ⟩
  orderL-fill = relL-fill boundOrd boundOrd-isL boundOrd-ord
```

<!--en-->
Conversely, membership of the encoded pair in `orderL` recovers the host-side comparison. Together, `orderL-fill` and `orderL-rep` say exactly which ordered pairs occur in the internal relation graph. They neither assert uniqueness of the set representing that graph nor prove within the object language that it is a well-order.
<!--zh-->
反过来，编码有序对属于 `orderL` 可恢复宿主层比较。`orderL-fill` 与 `orderL-rep` 合起来，逐对刻画哪些有序对出现在内部关系图中；它们既不声称表示该图的集合具有唯一性，也不在对象语言内部证明它是良序。
<!--ja-->
逆に、符号化された順序対が `orderL` に属することから、ホスト側の比較を復元できる。`orderL-fill` と `orderL-rep` を合わせると、どの順序対が内部の関係グラフに現れるかが要素ごとに正確に特徴づけられる。これらは、そのグラフを表す集合の一意性を主張せず、それが整列順序であることを対象言語の内部で証明するものでもない。
<!--/-->

```agda
  orderL-rep : (x y : Mem (Lset boundOrd))
             → ⟨ pr (fst x) (fst y) ∈ fst orderL ⟩ → relOf boundOrder x y
  orderL-rep = relL-rep boundOrd boundOrd-isL boundOrd-ord
```
</div>
</details>

<!--en-->
## Recap

The strict well-order remains the host-level structure `orderAt α oα`{.Agda} on `Mem (Lset α)`{.Agda}. The set `relL α hα oα`{.Agda} is an element of `L` that represents its binary relation as a graph, and `relL-fill`{.Agda} and `relL-rep`{.Agda} prove the two directions of that representation for each pair. The six-binder formula and its adequacy readings make this graph available to later object-language formulas, while proving neither a new well-order nor an object-language well-order assertion.
<!--zh-->
## 小结

严格良序仍是 `Mem (Lset α)`{.Agda} 上的宿主层结构 `orderAt α oα`{.Agda}。集合 `relL α hα oα`{.Agda} 是 `L` 的一个元素，它把该二元关系表示为关系图；`relL-fill`{.Agda} 与 `relL-rep`{.Agda} 对每一对元素证明这项表示的两个方向。六重绑定公式及其充分性读式使后续对象语言公式能够使用这个关系图，但既不证明新的良序，也不证明对象语言中的良序断言。
<!--ja-->
## まとめ

狭義整列順序そのものは、`Mem (Lset α)`{.Agda} 上のホスト側の構造 `orderAt α oα`{.Agda} である。集合 `relL α hα oα`{.Agda} は、その二項関係を関係グラフとして表す `L` の要素であり、`relL-fill`{.Agda} と `relL-rep`{.Agda} は、各要素対についてその表現の二方向を証明する。六つの束縛子をもつ論理式とその妥当性の読みは、この関係グラフを後の対象言語の論理式から利用できるようにするが、新しい整列順序も、対象言語における整列順序の主張も証明しない。
<!--/-->
