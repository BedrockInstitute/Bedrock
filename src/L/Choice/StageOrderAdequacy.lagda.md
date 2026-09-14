<!--en-->
# Adequacy of the stage-order description

The metatheory already carries a strict well order at every constructible stage, but the object language of `L` can speak only through formulas. This chapter translates that order into formulas: it describes the birth stage of each set, the code set that travels with each carrier, and the comparison rule of the stage order, proving that the descriptions are faithful to their meta-language meanings. One piece is deliberately left as a parameter: the comparison inside a fixed birth stage.
<!--zh-->
# 层序描述的充分性

元理论已经在每个可构造层携带一个严格良序，但 `L` 的对象语言只能通过公式说话。本章把这一层序翻译成公式：描述每个集合的诞生层、随载体变化的码集，以及层序的比较规则，并证明这些描述忠实于其元语言含义。其中有一件被刻意留作参数：固定诞生层内部的比较。
<!--ja-->
# 段階順序の記述の妥当性

メタ理論には、すでにすべての構成可能な段階で狭義の整列順序がありますが、`L` の対象言語は論理式を通してしか語れません。この章は、その順序を論理式へ翻訳します。各集合の誕生段階・台とともに動くコードの集合・段階順序の比較の規則を記述し、それらがメタ言語の意味に忠実であることを証明します。ただ一つ、意図的に引数のまま残したものがあります。固定された誕生段階の内部での比較です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
Classical reasoning enters through one explicit hypothesis, `lem`{.Agda}. It will be used when ordinal stages must be compared, while the formulas constructed in this chapter remain ordinary formulas of the object language. Thus a semantic argument may use excluded middle without inserting a new axiom into the language being interpreted.
<!--zh-->
经典推理只经由一个显式假设 `lem`{.Agda} 进入。比较序数层时会用到它，而本章构造的公式仍是对象语言的普通公式。因此，语义论证可以使用排中律，却不会把新公理写进被解释的语言。
<!--ja-->
古典的推論は、明示された一つの仮定 `lem`{.Agda} を通してだけ入ります。順序数段階を比較するときにこれを用いますが、この章で構成する論理式は対象言語の通常の論理式のままです。したがって、意味論的な議論で排中律を使っても、解釈される言語に新しい公理を加えることにはなりません。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Keep the two levels of discourse distinct from the outset. The previously constructed `orderAt`{.Agda} is a meta-language strict well order. The goal here is to build formulas whose satisfaction expresses its underlying comparison; no formula in this chapter reconstructs the `SWO`{.Agda} structure or reproves its well-foundedness.
<!--zh-->
从一开始就要区分两个话语层次。此前构造的 `orderAt`{.Agda} 是元语言中的严格良序。本章的目标是构造一些公式，使其满足关系表达该良序的底层比较；本章没有任何公式重新构造 `SWO`{.Agda} 结构，也不重证其良基性。
<!--ja-->
初めから二つの言語水準を区別しておきます。すでに構成された `orderAt`{.Agda} は、メタ言語における狭義の整列順序です。ここでの目標は、その基礎にある比較を充足によって表す論理式を作ることです。この章の論理式が `SWO`{.Agda} 構造を作り直したり、その整礎性を証明し直したりするわけではありません。
<!--/-->

```agda
module L.Choice.StageOrderAdequacy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The translation uses only the object language's ordinary atoms and connectives. Membership states that a proposed witness lies in a stage or code set, equality identifies two represented objects, and existential quantification hides the auxiliary sets needed by the description. Later proofs interpret these formulas in the constructible structure and compare the resulting propositions with their meta-language counterparts.
<!--zh-->
这次翻译只使用对象语言的普通原子与联结词。隶属原子陈述候选见证属于某层或码集，相等原子认同两个被表示的对象，而存在量词隐藏描述所需的辅助集合。后文的证明会在可构造结构中解释这些公式，再把所得命题与相应的元语言命题比较。
<!--ja-->
この翻訳で使うのは、対象言語の通常の原子式と結合子だけです。所属の原子式は候補となる証人が段階やコード集合に属することを述べ、等号の原子式は表現された二つの対象を同一視し、存在量化は記述に必要な補助集合を隠します。後の証明では、これらの論理式を構成可能な構造で解釈し、得られた命題を対応するメタ言語の命題と比較します。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim )
```

<!--en-->
The relevant geometry of the hierarchy is simple. Ordinals linearly order the stages, membership between ordinal indices makes the tower monotone, and the successor of an ordinal separates a stage from its next definable-power-set stage. These facts will let us identify a proposed birth ordinal by comparing its successor with the least stage at which the set appears.
<!--zh-->
这里所需的层级几何很简单。序数线性排列各层，序数指标之间的隶属使塔保持单调，而一个序数的后继把该层与下一可定义幂集层分开。借助这些事实，我们可以比较候选诞生序数的后继与集合首次出现的层，从而认定该候选序数。
<!--ja-->
ここで必要な階層の姿は単純です。順序数は各段階を線形に並べ、順序数の添字どうしの所属は塔を単調にし、ある順序数の後続はその段階と次の定義可能冪の段階を分けます。これらの事実により、候補となる誕生順序数の後続を、集合が初めて現れる段階と比較して、その候補を同定できます。
<!--/-->

```agda
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; isPropIsOrd; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
```

<!--en-->
For a constructible set `x`, its least containing stage is a successor, and `birth x`{.Agda} is the ordinal immediately below it. Consequently `x` is absent from `Lset (birth x)` but present in `Lset (sucV (birth x))`, which is the definable power set of the former stage. The formula `BirthAt`{.Agda} will express these two membership facts; leastness itself remains a meta-language theorem.
<!--zh-->
对可构造集合 `x`，包含它的最早层是一个后继层，而 `birth x`{.Agda} 是紧邻其下的序数。因此，`x` 不属于 `Lset (birth x)`，却属于 `Lset (sucV (birth x))`，后者正是前一层的可定义幂集。公式 `BirthAt`{.Agda} 将表达这两条隶属事实；最小性本身仍来自元语言定理。
<!--ja-->
構成可能集合 `x` を含む最初の段階は後続段階であり、`birth x`{.Agda} はその直前の順序数です。したがって `x` は `Lset (birth x)` には属さず、前者の定義可能冪である `Lset (sucV (birth x))` には属します。論理式 `BirthAt`{.Agda} が表すのはこの二つの所属事実であり、最小性そのものはメタ言語の定理から得られます。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ} using ( Lset-suc; LsetS; 𝒟ₒS; extensionalL )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( ord-suc-inj )
open import L.Choice.StageOrders {ℓ} lem
  using ( birth; birth-ord; birth-suc; birth-mem; birth-stage; birth-proof
```

<!--en-->
The existing stage order compares two members lexicographically by birth. An earlier birth decides the comparison immediately; equal births defer to the local order on the new elements of that stage. The later formula mirrors precisely this one unfolding equation, so its adequacy concerns the relation already carried by `orderAt`{.Agda}, not the construction of that order.
<!--zh-->
既有的层序按诞生层对两个成员作字典式比较。较早的诞生层立即决定比较；诞生层相等时，比较交给该层新生元素上的局部序。后面的公式将精确对应这一次展开方程，因此其充分性只关乎 `orderAt`{.Agda} 已经携带的关系，并不关乎该序的构造。
<!--ja-->
既存の段階順序は、二つの要素を誕生段階によって辞書式に比較します。誕生が早ければ比較はそこで決まり、誕生が等しければ、その段階の新しい要素上の局所順序に委ねられます。後で作る論理式は、この一回の展開方程式だけを正確に写します。したがって、その妥当性が対象とするのは `orderAt`{.Agda} がすでに備える関係であり、順序の構成ではありません。
<!--/-->

```agda
        ; Mem; New; relOf; carry; Under; stepAt
        ; orderAt; orderAt-step; module Family )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate )
open import L.Coding.Expressions {ℓ} using ( extAt; extAt-in; extAt-out; extAt-in-both )
```

<!--en-->
The same-stage comparison needs formulas over a carrier that varies with the common birth ordinal. Hence its syntax cannot be fixed once at a single stage. The code predicate used below ranges over every finite arity relative to a carrier held in a variable slot, allowing the carrier and its formula codes to move together.
<!--zh-->
同层比较需要使用定义在某个载体上的公式，而该载体随共同诞生序数变化。因此，相关语法不能预先固定在单一层上。下文的码谓词相对于一个由变元槽位持有的载体，涵盖每个有限元数，使载体及其公式码能够一同变化。
<!--ja-->
同じ段階の内部での比較には、共通の誕生順序数とともに変わる台上の論理式が必要です。そのため、使う構文を一つの段階にあらかじめ固定することはできません。以下のコード述語は、変数スロットに置かれた台に相対して、すべての有限アリティを扱い、台とその論理式コードを一緒に動かせるようにします。
<!--/-->

```agda
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.DefinablePowerSet {ℓ} lem using ( DefAt; DefAt-stage )
open import L.Coding.CodeSet {ℓ} lem
  using ( arityNumAtL; arityNumAtL-in; arityNumAtL-out; hasWitnessAt
        ; witnessAt-in; witnessAt-out; keyS; codeS
```

<!--en-->
The final target is a relation represented as a set of ordered pairs in `L`. A table below the ambient stage supplies local relation values, and the formula must agree with the meta-language comparison for every encoded pair. This agreement will require both correctness and existence of table entries, and it remains conditional on the two adequacy directions supplied for the local step formula.
<!--zh-->
最终目标是在 `L` 中把关系表示为有序对之集。环境层以下的一张表提供局部关系取值，而公式必须对每个编码有序对都与元语言比较一致。证明这种一致既需要表项的正确性，也需要表项的存在性，并且始终以局部步进公式的两条充分性读式为条件。
<!--ja-->
最終的な目標は、`L` の中で関係を順序対の集合として表すことです。周囲の段階より下の表が局所関係の値を与え、論理式は符号化された各順序対についてメタ言語の比較と一致しなければなりません。この一致には表の値の正しさと存在の両方が必要であり、局所ステップの論理式について与えられる二方向の妥当性を前提とします。
<!--/-->

```agda
        ; AllCodes; AllCodes-in; AllCodes-out; IsKeyOverAny )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Choice.OrderTable {ℓ} lem
  using ( Ordering; strict; Related; IsRel; Values; Entries
        ; related-in; module Described )
```

<!--en-->
An element of the represented relation is read as a code `pr u v`{.Agda}. Adequacy therefore has two tasks: recover some compared members `u` and `v` from such a pair code, and prove that their stage-order comparison holds; conversely, a known comparison must put the corresponding pair code into the represented set. The existence involved here is propositionally truncated, so it does not select a canonical decomposition.
<!--zh-->
被表示关系的一个元素读作编码 `pr u v`{.Agda}。因此，充分性有两个方向：从这种对码恢复某些被比较成员 `u`、`v` 并证明其层序比较成立；反过来，从一次已知比较把相应对码放入被表示集合。这里的存在经过命题截断，因而不会选出规范的分解。
<!--ja-->
表現された関係の要素は、コード `pr u v`{.Agda} として読まれます。したがって妥当性には二つの向きがあります。このような対のコードから比較される要素 `u` と `v` を何らかの形で取り出し、その段階順序による比較を示す向きと、既知の比較から対応する対のコードを表現集合に入れる向きです。ここでの存在は命題的切り詰めを受けているため、標準的な分解を選びません。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr )

```

<!--en-->
Several identifications in the proof transport relations along equal stage indices or equal pair codes. Because ordinality and constructibility evidence are propositions, changing such evidence does not change the mathematical object being represented. This proof irrelevance is what permits transport without turning certificates into additional choices.
<!--zh-->
证明中的若干认同会沿相等的层指标或对码搬运关系。由于序数性与可构造性证据都是命题，更换这些证据不会改变被表示的数学对象。正是这种证明无关性允许我们进行搬运，而不会把证书变成额外的选择。
<!--ja-->
証明では、等しい段階添字や等しい対のコードに沿って関係を何度か輸送します。順序数性と構成可能性の証拠は命題なので、それらの証拠を取り替えても、表現される数学的対象は変わりません。この証明無関係性により、証明書を余分な選択へ変えることなく輸送できます。
<!--/-->

```agda
import FOL.Absoluteness
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
Existential satisfaction is propositionally truncated throughout. A proof may use a stage value, a definable-power-set value, a decoded formula, or a table entry only when its target is again a proposition. In particular, none of the eliminations below yields a canonical witness, a chosen decoder, or a choice function assigning local relation values.
<!--zh-->
存在量词的满足关系始终经过命题截断。证明只有在目标仍是命题时，才能使用某个层取值、可定义幂集取值、解码公式或表项。因此，下文任何一次消去都不会给出规范见证、选定的解码器，或为局部关系指定取值的选择函数。
<!--ja-->
存在量化の充足は一貫して命題的切り詰めを受けています。段階の値、定義可能冪の値、復号された論理式、表の項を証明で使えるのは、行き先も命題である場合だけです。したがって、以下の除去から標準的な証人、選ばれた復号器、局所関係の値を割り当てる選択関数が得られることはありません。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
```

<!--en-->
Two successor constructions play different roles. `sucV`{.Agda} advances an ordinal stage, whereas numerals encode finite arities inside the hierarchy. Keeping them distinct prevents the statement that a set enters at the successor of its birth from being confused with the arity component of a formula code.
<!--zh-->
这里有两种作用不同的后继构造。`sucV`{.Agda} 推进一个序数层，而数码在层级内部编码有限元数。区分二者，就不会把「集合在诞生层的后继处进入」与公式码的元数分量混为一谈。
<!--ja-->
ここには役割の異なる二つの後続構成があります。`sucV`{.Agda} は順序数段階を一つ進め、数項は階層の内部で有限アリティを符号化します。両者を区別することで、集合が誕生段階の後続で現れるという事実と、論理式コードのアリティ成分とを混同せずに済みます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV; #_ )

```

<!--en-->
Formulas will be interpreted in the constructible structure `𝒮ʟ`{.Agda}. Their meanings are therefore proposition-valued: satisfaction records whether a described membership, equality, or existence holds inside `L`, while the proofs comparing those meanings live in the surrounding Cubical Agda metatheory.
<!--zh-->
这些公式将在可构造结构 `𝒮ʟ`{.Agda} 中解释，所以其含义取值于命题：满足关系记录被描述的隶属、相等或存在是否在 `L` 内成立，而比较这些含义的证明则生活在外围的 Cubical Agda 元理论中。
<!--ja-->
論理式は構成可能な構造 `𝒮ʟ`{.Agda} で解釈されるため、その意味は命題値です。充足は、記述された所属・等号・存在が `L` の内部で成り立つかを記録し、それらの意味を比較する証明は、周囲の Cubical Agda のメタ理論に属します。
<!--/-->

```agda
open hPropStructure 𝒮ʟ

```

<!--en-->
We write `γ ⊨ φ`{.Agda} for satisfaction at an environment and `⟦ t ⟧ γ`{.Agda} for the value of a term. This notation is the bridge used in every adequacy statement: the left side reads object-language syntax, while the right side identifies the corresponding set, ordinal, or relation in the metatheory.
<!--zh-->
我们以 `γ ⊨ φ`{.Agda} 表示公式在环境中的满足，以 `⟦ t ⟧ γ`{.Agda} 表示项的取值。每条充分性陈述都通过这套记号架桥：左侧读取对象语言语法，右侧认定元理论中相应的集合、序数或关系。
<!--ja-->
環境における論理式の充足を `γ ⊨ φ`{.Agda}、項の値を `⟦ t ⟧ γ`{.Agda} と書きます。この記法が、すべての妥当性の主張を結ぶ橋です。左辺は対象言語の構文を読み、右辺はメタ理論における対応する集合・順序数・関係を同定します。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )

```

<!--en-->
The first shift names the variable two slots outward, preparing the formulas that bind four objects.
<!--zh-->
第一个移位把变元命名到外移两槽的位置，为绑定四个对象的公式做准备。
<!--ja-->
最初のずらしは、変数を二つ外の枠に名前づけし、四つの対象を束縛する論理式のための準備をします。
<!--/-->

```agda
sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
sh2 i = suc (suc i)

```

<!--en-->
The second shift moves variables three slots outward.
<!--zh-->
第二个移位把变元外移三槽。
<!--ja-->
二つ目のずらしは、変数を三つ外の枠へ動かします。
<!--/-->

```agda
sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
sh3 i = suc (suc (suc i))

```

<!--en-->
A private shift moves variables four slots outward, reserved for the four-object bindings of the next section.
<!--zh-->
一个私有移位把变元外移四槽，预留给下一节绑定四个对象的公式。
<!--ja-->
非公開のずらしは、変数を四つ外の枠へ動かします。次の節で、四つの対象を束縛する論理式のために取っておかれたものです。
<!--/-->

```agda
private
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

```

<!--en-->
The term shift moves a term past four new bindings: constants keep their values, and each variable is renamed by the same shift.
<!--zh-->
项的移位把一个项移过四个新绑定：常数保持其值，每个变元按同一移位改名。
<!--ja-->
項のずらしは、一つの項を、新しく加わった四つの束縛の向こう側へ運びます。定数はその値を保ち、変数はどれも同じずらしで名前を変えます。
<!--/-->

```agda
  tm4 : ∀ {n} → Term S n → Term S (suc (suc (suc (suc n))))
  tm4 (con k) = con k
  tm4 (var i) = var (sh4 i)

```

<!--en-->
The evaluation of the shifted term is unaffected by the four extra bindings: this definitional agreement is recorded once and reused silently.
<!--zh-->
移位后的项的求值不受四个新绑定影响；这一定义性一致被记录一次，此后静默复用。
<!--ja-->
ずらされた項の評価は、新しく加わった四つの束縛の影響を受けません。この定義的な一致は一度記録され、その後は静かに再利用されます。
<!--/-->

```agda
  tm4-val : ∀ {n} (t : Term S n) (a b c d : S) (γ : S ^ n)
          → ⟦ tm4 t ⟧ (d ∷ c ∷ b ∷ a ∷ γ) ≡ ⟦ t ⟧ γ
  tm4-val (con k) a b c d γ = refl
  tm4-val (var i) a b c d γ = refl
```

<!--en-->
To place `Lset β` in a formula environment, we package the stage together with its constructibility proof as an element of `S`. The ordinalness hypothesis supplies that proof. What matters mathematically is the first projection recorded below: the package still denotes exactly `Lset β`, so it can serve as the stage witness when `BirthAt` is read inward.
<!--zh-->
为了把 `Lset β` 放入公式环境，我们将该层连同其可构造性证明打包为 `S` 的元素。序数性假设提供这份证明。数学上要紧的是下文的第一投影等式：这个封装仍恰好指称 `Lset β`，因而可以在向内读取 `BirthAt` 时充当层见证。
<!--ja-->
`Lset β` を論理式の環境に置くため、その段階を構成可能性の証明と組にして `S` の要素にします。順序数性の仮定がこの証明を与えます。数学的に重要なのは、次に示す第一射影の等式です。この包装が表す集合はちょうど `Lset β` なので、`BirthAt` を内向きに読む際の段階の証人として使えます。
<!--/-->

```agda
opaque
  towerS : (β : V ℓ) → IsOrd β → S
  towerS β ob = LsetS β ob

```

<!--en-->
The underlying set of the packaged stage is the stage itself, definitionally.
<!--zh-->
打包后的层的底层集按定义就是层本身。
<!--ja-->
まとめられた段階の底の集合は、定義により、その段階そのものです。
<!--/-->

```agda
  towerS-fst : (β : V ℓ) (ob : IsOrd β) → fst (towerS β ob) ≡ Lset β
  towerS-fst β ob = refl

```

<!--en-->
The second witness needed by `BirthAt` is the definable power set of that stage. We package `𝒟ₒ (Lset β)` in the same way; its constructibility follows from the stage facts available at the ordinal `β`, and its first projection is the set required by the formula.
<!--zh-->
`BirthAt` 所需的第二个见证是该层的可定义幂集。我们以同样方式封装 `𝒟ₒ (Lset β)`；它的可构造性来自序数 `β` 处已有的层事实，而其第一投影正是公式所需的集合。
<!--ja-->
`BirthAt` が必要とする第二の証人は、その段階の定義可能冪です。`𝒟ₒ (Lset β)` も同じように包装します。その構成可能性は順序数 `β` における段階の事実から従い、第一射影が論理式の要求する集合になります。
<!--/-->

```agda
  powS : (β : V ℓ) → IsOrd β → S
  powS β ob = 𝒟ₒS β ob

```

<!--en-->
Its underlying set is the definable power set of the stage at the ordinal, definitionally.
<!--zh-->
其底层集按定义就是该序数处层的可定义幂集。
<!--ja-->
その底の集合は、定義により、その順序数の段階の定義可能冪です。
<!--/-->

```agda
  powS-fst : (β : V ℓ) (ob : IsOrd β) → fst (powS β ob) ≡ 𝒟ₒ (Lset β)
  powS-fst β ob = refl
```

<!--en-->
## The birth stage, said inside
<!--zh-->
## 诞生层的内部表述
<!--ja-->
## 誕生段階を内部で述べる
<!--/-->

<!--en-->
`BirthAt b x`{.Agda} binds two auxiliary sets. The first is required to be the tower stage `Lset β` described at the candidate slot `b`; `x` must not belong to it. The second is required to be the definable power set of the first, and `x` must belong to it. Thus the formula expresses the boundary between two consecutive stages. It neither asserts that `β` is an ordinal nor contains an internal minimality clause.
<!--zh-->
`BirthAt b x`{.Agda} 绑定两个辅助集合。第一个必须是候选槽位 `b` 所描述的塔层 `Lset β`，且 `x` 不属于它；第二个必须是前者的可定义幂集，且 `x` 属于它。因此，该公式表达两个相继层之间的边界。它既不断言 `β` 是序数，也不包含对象语言内部的最小性子句。
<!--ja-->
`BirthAt b x`{.Agda} は二つの補助集合を束縛します。第一の集合は候補スロット `b` で記述される塔の段階 `Lset β` であり、`x` はそこに属しません。第二の集合は第一の集合の定義可能冪であり、`x` はそこに属します。したがって、この論理式は連続する二段階の境界を表します。`β` が順序数であるとは主張せず、対象言語内の最小性条件も含みません。
<!--/-->

```agda
BirthAt : ∀ {n} → Fin n → Fin n → Formula S n
BirthAt b x =
  ∃̇ ( LsetGraphAt zero (suc b)
    ∧̇ ( ¬̇ (var (suc x) ∈̇ var zero)
      ∧̇ ∃̇ ( DefAt zero (suc zero) ∧̇ (var (sh2 x) ∈̇ var zero) ) ) )
```

<!--en-->
Fix an environment `γ`. The candidate ordinal is the underlying set at slot `b`, while the set whose birth is being tested is the element at slot `x`. All subsequent reasoning is relative to these two interpretations, so the theorem concerns arbitrary variable assignments rather than specially chosen constants.
<!--zh-->
固定一个环境 `γ`。候选序数是槽位 `b` 中元素的底层集合，而待检验诞生层的集合是槽位 `x` 中的元素。后续推理都相对于这两个解释进行，所以定理适用于任意变元赋值，而非特选常元。
<!--ja-->
環境 `γ` を固定します。候補となる順序数はスロット `b` の要素の底の集合であり、誕生を調べる集合はスロット `x` の要素です。以下の議論はすべてこの二つの解釈に相対的なので、定理は特別に選んだ定数ではなく、任意の変数割り当てについて成り立ちます。
<!--/-->

```agda

module _ {n : ℕ} (b x : Fin n) (γ : S ^ n) where
  private
    β : V ℓ
    β = fst (lookup b γ)

```

<!--en-->
The element `z` carries both its underlying set and evidence that it belongs to `L`. The meta-language function `birth`{.Agda} uses that evidence to form an ordinal, but proof irrelevance ensures that the resulting ordinal does not encode a choice of constructibility proof.
<!--zh-->
元素 `z` 同时携带其底层集合与它属于 `L` 的证据。元语言函数 `birth`{.Agda} 使用这份证据形成一个序数，但证明无关性保证所得序数不会编码对某份可构造性证明的选择。
<!--ja-->
要素 `z` は、その底の集合と、それが `L` に属するという証拠をともに持ちます。メタ言語の関数 `birth`{.Agda} はその証拠を用いて順序数を作りますが、証明無関係性により、得られる順序数が構成可能性の証明の選択を符号化することはありません。
<!--/-->

```agda
    z : S
    z = lookup x γ

```

<!--en-->
The inner record collects a definable power set value `d` over the candidate stage `c`, together with satisfaction of the power-set description and the membership of the parameter in `d`.
<!--zh-->
内层记录收集候选层 `c` 之上的可定义幂集值 `d`，连同幂集描述的满足，以及参数属于 `d` 的隶属。
<!--ja-->
内側の記録は、候補の段階 `c` の上の定義可能冪の値 `d` と、冪の記述の充足、そして引数が `d` に属することを集めます。
<!--/-->

```agda
    Inner : S → Type (ℓ-suc ℓ)
    Inner c = Σ[ d ∈ S ]
      ( ⟨ (d ∷ c ∷ γ) ⊨ DefAt zero (suc zero) ⟩ × ⟨ fst z ∈ fst d ⟩ )

```

<!--en-->
The outer record adds the satisfaction of the stage graph at the raised index, the refutation of the parameter's membership in the candidate stage, and the truncation of the inner record. Together they are exactly what the birth formula asserts.
<!--zh-->
外层记录再加上「层图在抬升指数处的满足」「参数不属于候选层」的反驳，以及内层记录的截断。三者合起来恰是诞生公式所断言的内容。
<!--ja-->
外側の記録はさらに、上げられた添字のもとでの段階のグラフの充足、引数が候補の段階に属さないことの反証、そして内側の記録の切り詰めを加えます。三つ合わせて、これこそ誕生の論理式が主張することです。
<!--/-->

```agda
    Outer : S → Type (ℓ-suc ℓ)
    Outer c = ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
            × ( (⟨ fst z ∈ fst c ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥) × ∥ Inner c ∥₁ )

```

<!--en-->
The key semantic lemma assumes that `β` is an ordinal and that `x` lies in `𝒟ₒ (Lset β)` but not in `Lset β`. From precisely these boundary facts it proves `β ≡ birth x`{.Agda}. Ordinality is an input to this reading; it is not recovered from satisfaction of `BirthAt`{.Agda}.
<!--zh-->
关键语义引理假设 `β` 是序数，并且 `x` 属于 `𝒟ₒ (Lset β)` 而不属于 `Lset β`。它恰从这些边界事实证明 `β ≡ birth x`{.Agda}。序数性是这条读式的输入，并非从 `BirthAt`{.Agda} 的满足关系中恢复。
<!--ja-->
中心となる意味論的補題は、`β` が順序数であり、`x` が `𝒟ₒ (Lset β)` に属する一方で `Lset β` には属さないと仮定します。まさにこの境界の事実から `β ≡ birth x`{.Agda} を示します。順序数性はこの読みへの入力であり、`BirthAt`{.Agda} の充足から取り出されるものではありません。
<!--/-->

```agda
    decideBirth : IsOrd β → ⟨ fst z ∈ 𝒟ₒ (Lset β) ⟩
                → (⟨ fst z ∈ Lset β ⟩ → Empty.⊥)
                → β ≡ birth (fst z) (snd z)
    decideBirth ob hin hout = go (ord-tri (sucV β) (suc-ord ob)
                                          (stage (fst z) (snd z))
```

<!--en-->
Using `Lset-suc`{.Agda}, membership in `𝒟ₒ (Lset β)` becomes membership in `Lset (sucV β)`. This says that the least stage containing `x` occurs no later than the successor of `β`; the proof must still rule out every earlier possibility.
<!--zh-->
借助 `Lset-suc`{.Agda}，`𝒟ₒ (Lset β)` 中的隶属转化为 `Lset (sucV β)` 中的隶属。这说明包含 `x` 的最早层不晚于 `β` 的后继；证明还必须排除所有更早的可能。
<!--ja-->
`Lset-suc`{.Agda} により、`𝒟ₒ (Lset β)` への所属は `Lset (sucV β)` への所属に変わります。これは `x` を含む最初の段階が `β` の後続より後ではないことを意味しますが、さらに早い可能性をすべて排除する必要があります。
<!--/-->

```agda
                                          (stage-ord (fst z) (snd z)))
      where
      mem : ⟨ fst z ∈ Lset (sucV β) ⟩
      mem = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (Lset-suc β)) hin

```

<!--en-->
Suppose the least stage of `x` belonged to `sucV β`. Membership in a successor ordinal splits into two cases: that stage belongs to `β`, or it equals `β`. In either case, monotonicity or direct transport would put `x` in `Lset β`, contradicting the assumed nonmembership.
<!--zh-->
假设 `x` 的最早层属于 `sucV β`。后继序数中的隶属分成两种情形：该层属于 `β`，或该层等于 `β`。前一种由单调性、后一种由直接搬运，都会推出 `x` 属于 `Lset β`，与所假设的非隶属矛盾。
<!--ja-->
`x` の最初の段階が `sucV β` に属すると仮定します。後続順序数への所属は、その段階が `β` に属する場合と `β` に等しい場合に分かれます。前者では単調性により、後者では直接の輸送により、どちらも `x` が `Lset β` に属することになり、仮定した非所属に反します。
<!--/-->

```agda
      early : ⟨ stage (fst z) (snd z) ∈ sucV β ⟩ → Empty.⊥
      early h = Empty.rec* (∈sucV-elim {A = β} {x = stage (fst z) (snd z)}
        Empty.isProp⊥* h below same)
        where
        below : ⟨ stage (fst z) (snd z) ∈ β ⟩ → Empty.⊥*
```

<!--en-->
If `stage x ∈ β`, monotonicity carries the known membership of `x` in `Lset (stage x)` into `Lset β`. If `stage x ≡ β`, transport along that equality gives the same conclusion directly. Both alternatives contradict the boundary assumption `x ∉ Lset β`.
<!--zh-->
若 `stage x ∈ β`，层的单调性会把已知的 `x ∈ Lset (stage x)` 推到 `x ∈ Lset β`。若 `stage x ≡ β`，沿该等式搬运即可直接得到同一结论。两种情形都与边界假设 `x ∉ Lset β` 矛盾。
<!--ja-->
`stage x ∈ β` なら、段階の単調性により、既知の `x ∈ Lset (stage x)` から `x ∈ Lset β` が従います。`stage x ≡ β` なら、その等式に沿う輸送によって同じ結論が直接得られます。どちらも境界の仮定 `x ∉ Lset β` に反します。
<!--/-->

```agda
        below k = Empty.rec (hout
          (Lset-mono {α = β} {β = stage (fst z) (snd z)} k
            {x = fst z} (stage-mem (fst z) (snd z))))
        same : stage (fst z) (snd z) ≡ β → Empty.⊥*
        same e = Empty.rec (hout (subst (λ u → ⟨ fst z ∈ Lset u ⟩) e
```

<!--en-->
In the equality case, `stage x ≡ β` transports the known membership `x ∈ Lset (stage x)` to `x ∈ Lset β`. This is the second contradiction needed to show that the least stage cannot occur at or below `β`.
<!--zh-->
在相等情形中，`stage x ≡ β` 把已知的隶属 `x ∈ Lset (stage x)` 搬运成 `x ∈ Lset β`。这是证明最早层不可能位于 `β` 或其下所需的第二个矛盾。
<!--ja-->
等しい場合には、`stage x ≡ β` に沿って既知の所属 `x ∈ Lset (stage x)` を `x ∈ Lset β` へ輸送します。これが、最初の段階が `β` 以下にはありえないことを示すための第二の矛盾です。
<!--/-->

```agda
          (stage-mem (fst z) (snd z))))

```

<!--en-->
Ordinal trichotomy now compares `sucV β` with `stage x`. If the successor were strictly earlier, `x ∈ Lset (sucV β)` would contradict the defining minimality of `stage x`. If `stage x` were earlier, the preceding argument would contradict `x ∉ Lset β`. Hence only equality can remain.
<!--zh-->
现在用序数三歧律比较 `sucV β` 与 `stage x`。若前者严格更早，则 `x ∈ Lset (sucV β)` 与 `stage x` 的定义性最小性矛盾；若 `stage x` 更早，则前述论证与 `x ∉ Lset β` 矛盾。因此，只可能剩下相等情形。
<!--ja-->
ここで順序数の三岐性により `sucV β` と `stage x` を比較します。前者が真に早ければ、`x ∈ Lset (sucV β)` が `stage x` の定義上の最小性に反します。`stage x` が早ければ、直前の議論が `x ∉ Lset β` に反します。したがって、等しい場合だけが残ります。
<!--/-->

```agda
      go : ⟨ sucV β ∈ stage (fst z) (snd z) ⟩
         ⊎ ((sucV β ≡ stage (fst z) (snd z)) ⊎ ⟨ stage (fst z) (snd z) ∈ sucV β ⟩)
         → β ≡ birth (fst z) (snd z)
      go (inl h) = Empty.rec
        (stage-earliest (fst z) (snd z) (sucV β) (suc-ord ob) mem h)
```

<!--en-->
From `sucV β ≡ stage x`{.Agda} and the identity `stage x ≡ sucV (birth x)`{.Agda}, injectivity of ordinal successor gives `β ≡ birth x`{.Agda}. The conclusion is forced by exclusion of the two strict cases; the proof does not choose a birth witness from the formula.
<!--zh-->
由 `sucV β ≡ stage x`{.Agda} 与等式 `stage x ≡ sucV (birth x)`{.Agda}，序数后继的单射性给出 `β ≡ birth x`{.Agda}。结论来自对两个严格情形的排除；证明并未从公式中选取诞生见证。
<!--ja-->
`sucV β ≡ stage x`{.Agda} と `stage x ≡ sucV (birth x)`{.Agda} から、順序数の後続の単射性によって `β ≡ birth x`{.Agda} が得られます。結論は二つの狭義の場合を排除したことで強制されるのであり、論理式から誕生の証人を選んでいるのではありません。
<!--/-->

```agda
      go (inr (inl e)) = ord-suc-inj β (birth (fst z) (snd z)) ob
        (e ∙ sym (birth-suc (fst z) (snd z)))
      go (inr (inr h)) = Empty.rec (early h)

```

<!--en-->
The reading lemma carries the ordinalness hypothesis of the slot: the formula alone does not prove the slot to be an ordinal. The proof unwraps the truncated existential and reaches the outer record.
<!--zh-->
读取引理携带槽位的序数性假设：公式自身并不证明该槽位是序数。证明拆开截断的存在量化，抵达外层记录。
<!--ja-->
読みの補題は、その枠の順序数性の仮定を運びます。論理式だけでは、その枠が順序数であることを証明しません。証明は、切り詰められた存在量化を解いて、外側の記録に到達します。
<!--/-->

```agda
  BirthAt-out : ⟨ γ ⊨ BirthAt b x ⟩ → IsOrd β → β ≡ birth (fst z) (snd z)
  BirthAt-out h ob =
    PT.rec (setIsSet β (birth (fst z) (snd z))) atCarrier h
    where
    atInner : (c : S) → ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
```

<!--en-->
At each candidate stage, the inner record supplies a definable power set value containing the parameter, and the refutation of the parameter's membership in the candidate stage; the decision lemma is applied to these three data.
<!--zh-->
在每个候选层处，内层记录供给包含参数的可定义幂集值，以及参数不属于候选层的反驳；判定引理应用于这三份数据。
<!--ja-->
候補の段階ごとに、内側の記録は、引数を含む定義可能冪の値と、引数が候補の段階に属さないことの反証を供給します。判定の補題が、この三つのデータに適用されます。
<!--/-->

```agda
            → (⟨ fst z ∈ fst c ⟩ → Empty.⊥)
            → Inner c → β ≡ birth (fst z) (snd z)
    atInner c hg hn (d , (hd , hm)) = decideBirth ob
      (subst (λ u → ⟨ fst z ∈ u ⟩) qd hm)
      (λ k → hn (subst (λ u → ⟨ fst z ∈ u ⟩) (sym qc) k))
```

<!--en-->
The stage graph at the raised index is identified with the stage at the candidate ordinal by the uniqueness of the hierarchy description, and the power-set value is identified with the definable power set of that stage by the stage equation of the description.
<!--zh-->
抬升指数处的层图由层级描述的唯一性认同为候选序数处的层；幂集值由描述的层等式认同为该层的可定义幂集。
<!--ja-->
上げられた添字のもとでの段階のグラフは、階層の記述の一意性によって、候補の順序数の段階と同一視されます。そして冪の値は、記述の段階の等式によって、その段階の定義可能冪と同一視されます。
<!--/-->

```agda
      where
      qc : fst c ≡ Lset β
      qc = Lset-only zero (suc b) (c ∷ γ) hg ob
      qd : fst d ≡ 𝒟ₒ (Lset β)
      qd = subst ⟨_⟩ (DefAt-stage β ob zero (suc zero) (d ∷ c ∷ γ) qc) hd
```

<!--en-->
The outer record is eliminated into the inner reading, and the inner reading feeds the decision lemma; the whole proof eliminates the truncation into an equality of ordinals, which is a proposition.
<!--zh-->
外层记录被消去到内层读取，内层读取喂给判定引理；整个证明把截断消去为序数的相等，而序数相等是命题。
<!--ja-->
外側の記録は内側の読みへ消去され、内側の読みが判定の補題に渡されます。証明全体は、切り詰めを、順序数の等式という命題の中へ消去します。
<!--/-->

```agda

    atCarrier : Σ[ c ∈ S ] Outer c → β ≡ birth (fst z) (snd z)
    atCarrier (c , (hg , (hn , hi))) =
      PT.rec (setIsSet β (birth (fst z) (snd z)))
        (atInner c hg (λ k → lower (hn k))) hi

```

<!--en-->
For the converse direction, assume that the ordinal in slot `b` equals the meta-language birth of `x`. The two existential witnesses are the packaged stage `Lset β` and its packaged definable power set. They are placed under propositional truncation as required by existential satisfaction, so this construction does not assert that the formula has uniquely determined witnesses.
<!--zh-->
反向证明假设槽位 `b` 中的序数等于 `x` 的元语言诞生层。两个存在见证分别是打包后的层 `Lset β` 及其打包后的可定义幂集。按照存在满足关系的要求，它们被置于命题截断之下，所以这项构造并不声称公式具有唯一确定的见证。
<!--ja-->
逆向きでは、スロット `b` の順序数が `x` のメタ言語での誕生に等しいと仮定します。二つの存在証人には、包装された段階 `Lset β` と、その包装された定義可能冪を用います。存在量化の充足が要求する通り、これらは命題的切り詰めの中に置かれるので、この構成は論理式の証人が一意に定まるとは主張しません。
<!--/-->

```agda
  BirthAt-in : IsOrd β → β ≡ birth (fst z) (snd z) → ⟨ γ ⊨ BirthAt b x ⟩
  BirthAt-in ob e = ∣ towerS β ob
    , (hg , (hn , ∣ powS β ob , (hd , hm) ∣₁)) ∣₁
    where
    hg : ⟨ (towerS β ob ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
```

<!--en-->
The stage graph at the raised index holds because the packaged stage is the stage at that index, by the defining equation of the presentation.
<!--zh-->
抬升指数处的层图成立，因为打包后的层按呈现的定义等式就是该指数处的层。
<!--ja-->
上げられた添字のもとでの段階のグラフが成立するのは、まとめられた段階が、提示の定義の等式によって、その添字の段階だからです。
<!--/-->

```agda
    hg = Lset-defines zero (suc b) (towerS β ob ∷ γ) ob (towerS-fst β ob)

```

<!--en-->
If `x` belonged to `Lset β`, then after replacing `β` by `birth x`{.Agda}, it would occur at a stage strictly below `stage x = sucV (birth x)`{.Agda}. This contradicts `stage-earliest`{.Agda}, and supplies the negative membership required by `BirthAt`{.Agda}.
<!--zh-->
若 `x` 属于 `Lset β`，把 `β` 换成 `birth x`{.Agda} 后，它就会出现在严格低于 `stage x = sucV (birth x)`{.Agda} 的层。这与 `stage-earliest`{.Agda} 矛盾，从而给出 `BirthAt`{.Agda} 所需的非隶属。
<!--ja-->
もし `x` が `Lset β` に属するなら、`β` を `birth x`{.Agda} で置き換えることで、`x` は `stage x = sucV (birth x)`{.Agda} より真に低い段階ですでに現れることになります。これは `stage-earliest`{.Agda} に反し、`BirthAt`{.Agda} が要求する非所属を与えます。
<!--/-->

```agda
    hn : ⟨ fst z ∈ fst (towerS β ob) ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥
    hn k = lift (stage-earliest (fst z) (snd z) β ob
      (subst (λ u → ⟨ fst z ∈ u ⟩) (towerS-fst β ob) k)
      (subst (λ u → ⟨ u ∈ stage (fst z) (snd z) ⟩) (sym e)
        (birth-stage (fst z) (snd z))))
```

<!--en-->
The stage equation for `DefAt` identifies its satisfaction proposition with equality to `𝒟ₒ (Lset β)`. The projection equation for `powS β ob` supplies exactly that equality, so the packaged definable power set satisfies the required clause.
<!--zh-->
`DefAt` 的层等式把它的满足命题认同为与 `𝒟ₒ (Lset β)` 的相等。`powS β ob` 的投影等式恰好给出这项相等，因此封装后的可定义幂集满足所需子句。
<!--ja-->
`DefAt` の段階における等式は、その充足命題を `𝒟ₒ (Lset β)` との等しさに同一視します。`powS β ob` の射影の等式がまさにこの等しさを与えるので、包装された定義可能冪は必要な条項を満たします。
<!--/-->

```agda

    hd : ⟨ (powS β ob ∷ towerS β ob ∷ γ) ⊨ DefAt zero (suc zero) ⟩
    hd = subst ⟨_⟩
      (sym (DefAt-stage β ob zero (suc zero)
              (powS β ob ∷ towerS β ob ∷ γ) (towerS-fst β ob)))
      (powS-fst β ob)
```

<!--en-->
Finally, `birth-mem`{.Agda} places `x` in `Lset (sucV (birth x))`. Replacing the proposed ordinal by the birth ordinal, using `Lset-suc`{.Agda}, and then using the projection equation for the packaged power set transports this membership to the second witness. Together with the outward reading, this proves that `BirthAt`{.Agda} describes the birth ordinal exactly whenever the candidate slot is assumed ordinal; it adds neither internal ordinality nor canonical existential witnesses.
<!--zh-->
最后，`birth-mem`{.Agda} 把 `x` 放入 `Lset (sucV (birth x))`。先把候选序数换成诞生序数，再使用 `Lset-suc`{.Agda}，最后使用打包可定义幂集的投影等式，就把这条隶属搬运到第二个见证中。结合向外读式，这证明了在候选槽位被假设为序数时，`BirthAt`{.Agda} 精确描述诞生序数；它既不在内部添加序数性，也不给出规范的存在见证。
<!--ja-->
最後に、`birth-mem`{.Agda} は `x` を `Lset (sucV (birth x))` に入れます。候補順序数を誕生順序数で置き換え、`Lset-suc`{.Agda} を使い、さらに包装された定義可能冪の射影方程式を使うことで、この所属を第二の証人へ輸送します。外向きの読みと合わせると、候補スロットが順序数であると仮定した場合に `BirthAt`{.Agda} が誕生順序数を正確に記述することが分かります。内部で順序数性を加えることも、標準的な存在証人を与えることもありません。
<!--/-->

```agda

    hm : ⟨ fst z ∈ fst (powS β ob) ⟩
    hm = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (powS-fst β ob))
      (subst (λ u → ⟨ fst z ∈ u ⟩) (Lset-suc β)
        (subst (λ u → ⟨ fst z ∈ Lset (sucV u) ⟩) (sym e)
          (birth-mem (fst z) (snd z))))
```

<!--en-->
## The codes at any arity, at a carrier held in a slot
<!--zh-->
## 任意元数处的诸码，位于槽位所持的载体上
<!--ja-->
## スロットにある台上の任意アリティの符号
<!--/-->

<!--en-->
The per-code recognizer combines two clauses: the first reads an arity numeral from the code, and the second checks that the code witnesses a formula over the working alphabet. Together they say the code is a genuine formula code at some arity.
<!--zh-->
逐码识别式合并两个子句：第一个从码读取元数数码，第二个检查该码见证工作字母表上的一条公式。二者合起来说该码是某个元数处的真公式码。
<!--ja-->
符号ごとの認識式は、二つの条項を合わせます。最初の条項が符号からアリティの数項を読み、二つ目の条項が、その符号が作業のアルファベットの上の論理式の証人であることを確認します。合わせて、その符号がなんらかのアリティでの本物の論理式の符号であると言います。
<!--/-->

```agda
isCodeAnyAt : ∀ {n} → Fin n → Fin n → Formula S n
isCodeAnyAt c w = arityNumAtL c ∧̇ hasWitnessAt w c

```

<!--en-->
The inward reading is stated for a working set `A`, two slots, an environment aligned with `A`, a formula of arity `k`, and the equation identifying the code slot with the key of that formula. It fills both conjuncts.
<!--zh-->
向内读式以工作集 `A`、两个槽位、与 `A` 对齐的环境、元数 `k` 的公式、以及认同码槽与该公式键的等式为参数。它填充两个合取项。
<!--ja-->
内向きの読み出しは、作業集合 `A`、二つの枠、`A` と揃った環境、アリティ `k` の論理式、そして符号の枠をその論理式のキーと同一視する等式に対して述べられ、二つの連言項を満たします。
<!--/-->

```agda
module _ (A : S) where
  codeAnyAt-in : ∀ {n k} (c w : Fin n) (γ : S ^ n)
               → fst (lookup w γ) ≡ fst A
               → (ψ : Formula ⟪ fst A ⟫ k) → fst (lookup c γ) ≡ fst (keyS A ψ)
               → ⟨ γ ⊨ isCodeAnyAt c w ⟩
```

<!--en-->
The two conjuncts are filled by their own inward readings: the arity reading names the natural number and the code, and the witness reading confirms the formula is over the aligned alphabet.
<!--zh-->
两个合取项由各自的向内读式填充：元数读法名指自然数与码，见证读式确认该公式在已对齐的字母表上。
<!--ja-->
二つの連言項は、それぞれの内向きの読み出しで満たされます。アリティの読み出しが自然数と符号を名指し、証人の読み出しが、論理式が揃えられたアルファベットの上にあることを確認します。
<!--/-->

```agda
  codeAnyAt-in {k = k} c w γ qw ψ qc =
    arityNumAtL-in c γ k (codeS A ψ) qc , witnessAt-in A w c γ ψ qw qc

```

<!--en-->
The outward reading recovers the truncated code witness: some arity and some formula produce this key. The truncated data stays inside propositional truncation.
<!--zh-->
向外读法恢复截断的码见证：某个元数与某条公式产生此键。截断数据保持在命题截断之内。
<!--ja-->
外向きの読み出しが、切り詰められた符号の証人を復元します。あるアリティとある論理式がこのキーを作ります。切り詰められたデータは、命題の切り詰めの中にとどまります。
<!--/-->

```agda
  codeAnyAt-out : ∀ {n} (c w : Fin n) (γ : S ^ n)
                → fst (lookup w γ) ≡ fst A
                → ⟨ γ ⊨ isCodeAnyAt c w ⟩
                → ⟨ IsKeyOverAny A (lookup c γ) ⟩
  codeAnyAt-out c w γ qw (hk , hw) =
```

<!--en-->
The proof eliminates the arity reading into a pair of a natural number and a code, then maps the witness reading into the code-level truncated existence.
<!--zh-->
证明消去元数读取为自然数与码的对，再把见证读法映入码层级的截断存在。
<!--ja-->
証明は、アリティの読み出しを、自然数と符号の対の中へ消去し、証人の読み出しを、符号のレベルの切り詰められた存在の中へ写像します。
<!--/-->

```agda
    PT.rec squash₁ step (arityNumAtL-out c γ hk)
    where
    step : Σ[ m ∈ ℕ ] Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# m) (fst z))
         → ⟨ IsKeyOverAny A (lookup c γ) ⟩
    step (m , (z , qz)) = PT.map (λ { (ψ , q) → m , (ψ , q) })
```

<!--en-->
The witness-reading elimination recovers the formula and the code equation at the correct arity, completing the truncated existence.
<!--zh-->
见证读法的消去在正确元数处恢复公式与码等式，完成截断存在。
<!--ja-->
証人の読み出しの消去が、正しいアリティで論理式と符号の等式を復元し、切り詰められた存在を完成させます。
<!--/-->

```agda
      (witnessAt-out A w c γ qw hw m z qz)
```

<!--en-->
## The set, in one extension
<!--zh-->
## 那个集合，一次外延
<!--ja-->
## 符号集合を一度の外延性で得る
<!--/-->

<!--en-->
`CodesAt c w` does not construct a code set. Through `extAt`, it describes the set already occupying slot `c`: an element belongs to that set exactly when it is the key of some finite-arity formula over the carrier in slot `w`. This determines the slot value extensionally as `AllCodes A`, while every formula witness used in the membership reading remains propositionally truncated.
<!--zh-->
`CodesAt c w` 并不构造码集。它借助 `extAt` 描述已经占据槽位 `c` 的集合：一个元素属于该集合，当且仅当它是槽位 `w` 所持载体上某个有限元数公式的键。这样便在外延意义上把槽位取值确定为 `AllCodes A`，而隶属读式所用的每个公式见证仍处于命题截断之下。
<!--ja-->
`CodesAt c w` は符号集合を構成するのではありません。`extAt` を通して、すでにスロット `c` にある集合を記述します。その集合に属する要素は、スロット `w` の台上の、ある有限アリティの論理式のキーであり、またそのときに限ります。これによりスロットの値は外延的に `AllCodes A` と定まりますが、所属の読みで用いる論理式の証人はすべて命題的に切り詰められたままです。
<!--/-->

```agda
CodesAt : ∀ {n} → Fin n → Fin n → Formula S n
CodesAt c w = extAt c (isCodeAnyAt zero (suc w))

```

<!--en-->
The outward reading of the code set says that the slot holds exactly the code set of the working alphabet. The proof is by extensionality in two directions.
<!--zh-->
码集的向外读法说：该槽位恰持有工作字母表的码集。证明沿两个方向作外延性。
<!--ja-->
符号の集合の外向きの読み出しは、その枠が作業のアルファベットの符号の集合をちょうど保持すると言います。証明は、二方向で外延性によって進みます。
<!--/-->

```agda
module _ (A : S) {n : ℕ} (c w : Fin n) (γ : S ^ n)
         (qw : fst (lookup w γ) ≡ fst A) where
  CodesAt-out : ⟨ γ ⊨ CodesAt c w ⟩ → lookup c γ ≡ AllCodes A
  CodesAt-out h = extensionalL step
    where
```

<!--en-->
For the first inclusion, `codeAnyAt-out` turns membership in the described slot into the propositionally truncated assertion that the element is a formula key. `AllCodes-in` turns precisely that assertion into membership in the fixed meta-language set `AllCodes A`; no particular decoding is selected.
<!--zh-->
对第一项包含，`codeAnyAt-out` 把描述槽位中的隶属读成「该元素是某条公式之键」的命题截断。`AllCodes-in` 恰把这项断言化为对固定元语言集合 `AllCodes A` 的隶属，并不选出某个特定解码。
<!--ja-->
第一の包含では、`codeAnyAt-out` が、記述されたスロットへの所属を「その要素はある論理式のキーである」という命題的切り詰めへ読み替えます。`AllCodes-in` はまさにこの主張を、固定されたメタ言語の集合 `AllCodes A` への所属へ変えます。特定の復号が選ばれることはありません。
<!--/-->

```agda
    step : (x : S) → (x ∈ˢ lookup c γ) ≡ (x ∈ˢ AllCodes A)
    step x = ⇔toPath
      (λ hx → AllCodes-in A x
        (codeAnyAt-out A zero (suc w) (x ∷ γ) qw
          (extAt-out c (isCodeAnyAt zero (suc w)) γ h x hx)))
```

<!--en-->
For the reverse inclusion, membership in `AllCodes A` gives only the propositional truncation of an arity and a formula whose key is the given element. Since satisfaction of the per-code formula is itself a proposition, the proof may eliminate that truncation there and apply `codeAnyAt-in`. No distinguished decoding is extracted.
<!--zh-->
为证明反向包含，`AllCodes A` 中的隶属只给出一个元数与一条公式的命题截断，并说明给定元素是该公式的键。逐码公式的满足本身是命题，所以证明可以在此处消去该截断并应用 `codeAnyAt-in`，但不会提取出一份指定的解码。
<!--ja-->
逆向きの包含では、`AllCodes A` への所属から得られるのは、与えられた要素をキーにもつアリティと論理式の命題的切り詰めだけです。符号ごとの論理式の充足は命題なので、そこで切り詰めを除去して `codeAnyAt-in` を適用できます。ただし、特定の復号が取り出されるわけではありません。
<!--/-->

```agda
      (λ hx → extAt-in c (isCodeAnyAt zero (suc w)) γ h x
        (PT.rec (snd ((x ∷ γ) ⊨ isCodeAnyAt zero (suc w)))
          (λ { (k , (ψ , q)) →
                 codeAnyAt-in A {k = k} zero (suc w) (x ∷ γ) qw ψ q })
          (AllCodes-out A x hx)))
```

<!--en-->
Conversely, suppose the value in slot `c` is equal to `AllCodes A`. To prove `CodesAt`, it remains to establish the two membership implications required by the extension formula: a member of the slot satisfies the per-code predicate, and anything satisfying that predicate belongs to the slot.
<!--zh-->
反过来，设槽位 `c` 的取值等于 `AllCodes A`。要证明 `CodesAt`，只需给出外延公式要求的两条隶属蕴含：槽位中的成员满足逐码谓词，而满足该谓词的对象属于槽位。
<!--ja-->
逆に、スロット `c` の値が `AllCodes A` に等しいとします。`CodesAt` を示すには、外延を述べる論理式が要求する二つの所属の含意を示せば十分です。すなわち、スロットの要素は符号ごとの述語を満たし、その述語を満たすものはスロットに属します。
<!--/-->

```agda

  CodesAt-in : lookup c γ ≡ AllCodes A → ⟨ γ ⊨ CodesAt c w ⟩
  CodesAt-in q = extAt-in-both c (isCodeAnyAt zero (suc w)) γ into back
    where
    into : (x : S) → ⟨ fst x ∈ fst (lookup c γ) ⟩
         → ⟨ (x ∷ γ) ⊨ isCodeAnyAt zero (suc w) ⟩
```

<!--en-->
For the first implication, the equality of sets turns slot membership into membership in `AllCodes A`. The latter supplies a formula witness only under propositional truncation, which may be eliminated into the proposition expressing satisfaction of `isCodeAnyAt`.
<!--zh-->
对第一条蕴含，集合等式把槽位隶属化为 `AllCodes A` 中的隶属。后者只在命题截断下给出公式见证；由于目标是 `isCodeAnyAt` 的满足命题，可以把截断消去到这个目标中。
<!--ja-->
第一の含意では、集合の等式によってスロットへの所属を `AllCodes A` への所属へ移します。そこから論理式の証人が得られるのは命題的切り詰めのもとだけですが、目標は `isCodeAnyAt` の充足という命題なので、その目標へ切り詰めを除去できます。
<!--/-->

```agda
    into x hx = PT.rec (snd ((x ∷ γ) ⊨ isCodeAnyAt zero (suc w)))
      (λ { (k , (ψ , qk)) →
             codeAnyAt-in A {k = k} zero (suc w) (x ∷ γ) qw ψ qk })
      (AllCodes-out A x (subst (λ u → ⟨ fst x ∈ fst u ⟩) q hx))

```

<!--en-->
For the converse implication, `codeAnyAt-out` turns satisfaction into the truncated assertion that the candidate is some formula key. `AllCodes-in` uses precisely that assertion to prove membership in `AllCodes A`, and the set equality transports the result back to slot `c`.
<!--zh-->
对反向蕴含，`codeAnyAt-out` 把满足关系读成「候选对象是某条公式之键」的命题截断。`AllCodes-in` 正用这条截断断言证明对象属于 `AllCodes A`，随后集合等式把结论搬回槽位 `c`。
<!--ja-->
逆向きの含意では、`codeAnyAt-out` が充足を「候補はある論理式のキーである」という命題的切り詰めへ読み替えます。`AllCodes-in` はまさにこの切り詰められた主張から `AllCodes A` への所属を示し、集合の等式がその結論をスロット `c` へ戻します。
<!--/-->

```agda
    back : (x : S) → ⟨ (x ∷ γ) ⊨ isCodeAnyAt zero (suc w) ⟩
         → ⟨ fst x ∈ fst (lookup c γ) ⟩
    back x hx = subst (λ u → ⟨ fst x ∈ fst u ⟩) (sym q)
      (AllCodes-in A x (codeAnyAt-out A zero (suc w) (x ∷ γ) qw hx))
```

<!--en-->
## The order at a stage, unfolded once
<!--zh-->
## 层处的序，展开一次
<!--ja-->
## 段階の順序を一度だけ展開する
<!--/-->

<!--en-->
At an ordinal `δ`, the already constructed order `orderAt δ` compares members of `Lset δ`. Transporting that order to the small carrier expected by the naming construction lets `stepAt δ` build the local strict well-order `stepOrder δ` on `New δ`, the members of `Lset (sucV δ)`.
<!--zh-->
在序数 `δ` 处，前章已经构造的 `orderAt δ` 比较 `Lset δ` 的成员。把该序搬到命名构造所需的小载体后，`stepAt δ` 据此在 `New δ`，即 `Lset (sucV δ)` 的成员上构造局部严格良序 `stepOrder δ`。
<!--ja-->
順序数 `δ` では、前章ですでに構成された `orderAt δ` が `Lset δ` の要素を比較します。その順序を名前の構成が要求する小さい台へ移すことで、`stepAt δ` は `New δ`、すなわち `Lset (sucV δ)` の要素上に局所的な狭義整列順序 `stepOrder δ` を作ります。
<!--/-->

```agda
stepOrder : (δ : V ℓ) → IsOrd δ → SWO (New δ)
stepOrder δ oδ = stepAt δ (carry (Lset δ) (orderAt δ oδ))

```

<!--en-->
If `δ ≡ δ'`, an `Under` comparison at `δ` transports to one at `δ'`. The dependent pair path also reconciles the two proofs that the carrier is ordinal; this is valid because `IsOrd` is a proposition. Thus the transported comparison does not depend on a chosen ordinality certificate.
<!--zh-->
若 `δ ≡ δ'`，则 `δ` 处的 `Under` 比较可搬运到 `δ'` 处。依赖对的路径同时认同两份序数性证明；这是因为 `IsOrd` 是命题。因此，搬运后的比较不依赖于所选的序数性证书。
<!--ja-->
`δ ≡ δ'` なら、`δ` での `Under` の比較を `δ'` での比較へ輸送できます。依存対のパスは、台が順序数であることの二つの証明も同時に一致させます。これは `IsOrd` が命題だから可能です。したがって、輸送された比較は、選んだ順序数性の証明に依存しません。
<!--/-->

```agda
stepMoved : (δ δ' : V ℓ) (e : δ ≡ δ') (o : IsOrd δ) (o' : IsOrd δ') (x y : V ℓ)
          → Under δ (stepOrder δ o) x y → Under δ' (stepOrder δ' o') x y
stepMoved δ δ' e o o' x y =
  subst (λ p → Under (fst p) (stepOrder (fst p) (snd p)) x y)
    (Σ≡Prop isPropIsOrd {u = δ , o} {v = δ' , o'} e)
```

<!--en-->
Suppose the birth ordinal of a constructible set `x` belongs to an ordinal `α`. Then the successor of that birth is either a member of `α` or equal to `α`. Since `x` belongs to the level at that successor, either alternative places `x` in `Lset α`.
<!--zh-->
设可构造集合 `x` 的诞生序数属于序数 `α`。那么该诞生序数的后继要么属于 `α`，要么等于 `α`。由于 `x` 属于以该后继为指标的层，这两种情形都会把 `x` 放入 `Lset α`。
<!--ja-->
構成可能集合 `x` の誕生順序数が順序数 `α` に属するとします。その誕生順序数の後続は、`α` に属するか `α` に等しいかのどちらかです。`x` はその後続を添字とする段階に属するので、どちらの場合も `x` を `Lset α` に置けます。
<!--/-->

```agda

bornIn : (α : V ℓ) → IsOrd α → (x : V ℓ) (p : ⟨ isL x ⟩)
       → ⟨ birth x p ∈ α ⟩ → ⟨ x ∈ Lset α ⟩
bornIn α oα x p h = reach (suc∈or≡ (birth x p) α (birth-ord x p) oα h)
  where
  reach : ⟨ sucV (birth x p) ∈ α ⟩ ⊎ (sucV (birth x p) ≡ α) → ⟨ x ∈ Lset α ⟩
```

<!--en-->
The two alternatives supplied by `suc∈or≡` finish the argument. If the successor birth belongs to `α`, monotonicity carries `birth-mem` up to `Lset α`; if it equals `α`, transport along the equality gives the same membership directly.
<!--zh-->
`suc∈or≡` 给出的两种情形完成了论证。若诞生序数的后继属于 `α`，单调性把 `birth-mem` 推到 `Lset α`；若该后继等于 `α`，沿等式搬运即可直接得到同一隶属。
<!--ja-->
`suc∈or≡` が与える二つの場合で議論は完了します。誕生順序数の後続が `α` に属するなら、単調性によって `birth-mem` を `Lset α` まで運べます。その後続が `α` に等しいなら、等式に沿う輸送によって同じ所属が直接得られます。
<!--/-->

```agda
  reach (inl k) = Lset-mono {α = α} {β = sucV (birth x p)} k
    {x = x} (birth-mem x p)
  reach (inr e) = subst (λ w → ⟨ x ∈ Lset w ⟩) e (birth-mem x p)

```

<!--en-->
Now fix an ambient ordinal `α`. Every member of `Lset α` has a birth ordinal below `α`, so the earlier-stage orders needed by the recursive equation for `orderAt α` are available at exactly the required indices. This lets us state the equation as a direct comparison of the two members' births.
<!--zh-->
现在固定环境序数 `α`。`Lset α` 的每个成员都有一个低于 `α` 的诞生序数，因此 `orderAt α` 的递归方程所需的较早层序恰在相应指标处可用。于是，我们可以把该方程直接表成两个成员的诞生层比较。
<!--ja-->
周囲の順序数 `α` を固定します。`Lset α` の各要素は `α` より下の誕生順序数をもつので、`orderAt α` の再帰方程式が必要とする前段階の順序は、ちょうど必要な添字で利用できます。これにより、その方程式を二つの要素の誕生段階の比較として直接述べられます。
<!--/-->

```agda
module _ (α : V ℓ) (oα : IsOrd α) where
  private
    module Fam = Family α (λ δ _ → orderAt δ) oα

```

<!--en-->
Every layer member is constructible, by the layer's constructibility and transitivity along membership.
<!--zh-->
每个层成员可构造，由层的可构造性与沿隶属的传递性而来。
<!--ja-->
層のすべての要素は構成可能です。層の構成可能性と、所属に沿う推移性によるものです。
<!--/-->

```agda
  memberL : (a : Mem (Lset α)) → ⟨ isL (fst a) ⟩
  memberL a = Lset→isL α oα (fst a) (snd a)

```

<!--en-->
Because every member `a` of `Lset α` is constructible, it has a birth ordinal. We write this ordinal as `bornOf a`; it will be the primary key when the order at `α` is unfolded.
<!--zh-->
由于 `Lset α` 的每个成员 `a` 都可构造，它都有诞生序数。把这个序数记为 `bornOf a`；展开 `α` 处的序时，它将作为第一比较键。
<!--ja-->
`Lset α` の各要素 `a` は構成可能なので、誕生順序数をもちます。この順序数を `bornOf a` と書きます。これは `α` での順序を展開するときの第一の比較キーになります。
<!--/-->

```agda
  bornOf : (a : Mem (Lset α)) → V ℓ
  bornOf a = birth (fst a) (memberL a)

```

<!--en-->
The fact `bornOf a ∈ α` has two roles. It confirms that the birth ordinal is available as an earlier index in the unfolding of `orderAt α`, and later it lets `bornIn` recover `a` as a member of the ambient stage from an object-language birth description.
<!--zh-->
事实 `bornOf a ∈ α` 有两项作用。它先确认该诞生序数可在展开 `orderAt α` 时充当较早指标；随后又使 `bornIn` 能从对象语言的诞生描述恢复 `a` 对环境层的隶属。
<!--ja-->
`bornOf a ∈ α` という事実には二つの役割があります。まず、`orderAt α` の展開で誕生順序数を前段階の添字として使えることを保証します。さらに後では、対象言語による誕生の記述から、`bornIn` によって `a` の周囲の段階への所属を回復できます。
<!--/-->

```agda
  bornMem : (a : Mem (Lset α)) → ⟨ bornOf a ∈ α ⟩
  bornMem a = Fam.bornAt a .snd

```

<!--en-->
The unfolding equation is the connection point of the chapter. It says: the order at `α` holds between `a` and `b` exactly when either the birth ordinal of `a` is strictly below that of `b`, or they share the same birth ordinal and the local step order at that birth ordinal places `a` below `b`.
<!--zh-->
展开等式是本章的连接点。它说：`α` 处的序在 `a` 与 `b` 之间成立，恰当 `a` 的诞生序数严格低于 `b` 的诞生序数，或二者共享同一诞生序数且该诞生序数处的局部步进序把 `a` 置于 `b` 之下。
<!--ja-->
展開の等式が、本章の接続点です。`α` での順序が `a` と `b` の間で成立するのは、`a` の誕生の順序数が `b` のそれより厳密に下にあるか、あるいは、同じ誕生の順序数を共有していて、その誕生の順序数での局所のステップの順序が `a` を `b` の下に置くときで、そのときに限ります。
<!--/-->

```agda
  order-unfold : (a b : Mem (Lset α))
               → relOf (orderAt α oα) a b
               ≡ ( ⟨ bornOf a ∈ bornOf b ⟩
                 ⊎ ( (bornOf b ≡ bornOf a)
                   × Under (bornOf a) (stepOrder (bornOf a)
```

<!--en-->
The proof uses `orderAt-step` to expose one layer of the membership recursion and then applies congruence to its underlying relation. It therefore derives the two-case equation from the order constructed in the previous chapter; it does not construct or reprove that strict well-order here.
<!--zh-->
证明用 `orderAt-step` 展开一层隶属递归，再对其底层关系应用同余。因此，这个两分等式来自前章已经构造的序；此处既不重新构造也不重新证明该严格良序。
<!--ja-->
証明は `orderAt-step` で所属再帰を一段だけ開き、その基礎にある関係へ合同性を適用します。したがって、この二場合の等式は前章で構成済みの順序から導かれます。ここでその狭義整列順序を構成し直したり、証明し直したりはしません。
<!--/-->

```agda
                       (mem-ord {A = α} oα (bornOf a) (bornMem a)))
                       (fst a) (fst b) ) )
  order-unfold a b = cong (λ z → relOf (z oα) a b) (orderAt-step α)
```

<!--en-->
The member-to-carrier wrapper packages each layer member as a carrier element, so that the formula environment can hold it.
<!--zh-->
成员到载体的包装把每个层成员打包为载体元素，使公式环境能容纳它。
<!--ja-->
要素から台への包みが、層のそれぞれの要素を台の要素としてまとめ、論理式の環境がそれを収められるようにします。
<!--/-->

```agda
opaque
  memS : (α : V ℓ) (oα : IsOrd α) → Mem (Lset α) → S
  memS α oα a = fst a , memberL α oα a

```

<!--en-->
The first-projection equation confirms the packaging preserves the underlying set.
<!--zh-->
第一投影等式确认包装保持底层集合。
<!--ja-->
第一射影の等式が、まとめが基礎の集合を保つことを確認します。
<!--/-->

```agda
  memS-fst : (α : V ℓ) (oα : IsOrd α) (a : Mem (Lset α))
           → fst (memS α oα a) ≡ fst a
  memS-fst α oα a = refl

```

<!--en-->
The birth presentation packages the birth ordinal with the constructibility transported from the enclosing ordinal `α`.
<!--zh-->
诞生呈现把诞生序数连同从外围序数 `α` 运来的可构造性打包。
<!--ja-->
誕生の提示は、誕生の順序数と、包む順序数 `α` から運ばれた構成可能性を対にします。
<!--/-->

```agda
  bornS : (α : V ℓ) (oα : IsOrd α) → ⟨ isL α ⟩ → Mem (Lset α) → S
  bornS α oα pα a = bornOf α oα a
                  , isL-trans {x = α} {y = bornOf α oα a} (bornMem α oα a) pα

```

<!--en-->
The first-projection equation confirms the packaging preserves the birth ordinal.
<!--zh-->
第一投影等式确认包装保持诞生序数。
<!--ja-->
第一射影の等式が、まとめが誕生の順序数を保つことを確認します。
<!--/-->

```agda
  bornS-fst : (α : V ℓ) (oα : IsOrd α) (pα : ⟨ isL α ⟩) (a : Mem (Lset α))
            → fst (bornS α oα pα a) ≡ bornOf α oα a
  bornS-fst α oα pα a = refl

```

<!--en-->
The birth equation confirms the packaged birth matches the computed birth of the packaged member.
<!--zh-->
诞生等式确认打包的诞生与打包成员的计算诞生一致。
<!--ja-->
誕生の等式が、まとめられた誕生が、まとめられた要素の計算された誕生と一致することを確認します。
<!--/-->

```agda
  bornS-birth : (α : V ℓ) (oα : IsOrd α) (pα : ⟨ isL α ⟩) (a : Mem (Lset α))
              → fst (bornS α oα pα a)
              ≡ birth (fst (memS α oα a)) (snd (memS α oα a))
  bornS-birth α oα pα a = refl
```

<!--en-->
## The order described, with the step as a parameter
<!--zh-->
## 那个序，被描述出来，而那一步取作参数
<!--ja-->
## ステップをパラメータとして順序を記述する
<!--/-->

<!--en-->
The step-formula type is a four-slot formula family, parameterized by the carrier slot, the table slot, and the two comparison slots.
<!--zh-->
步进公式类型是四槽公式族，以载体槽、表槽与两个比较槽为参数。
<!--ja-->
ステップの論理式の型は、台の枠・表の枠・そして比較のための二つの枠をパラメータとする、四つの枠の論理式の族です。
<!--/-->

```agda
StpFo : Type (ℓ-suc ℓ)
StpFo = ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n

```

<!--en-->
The outward adequacy reading is relative to an ordinal carrier `d`, a table `f`, and two compared objects. Its table hypothesis says that every value `r` recorded at `d` realizes the stage relation `IsRel d r`. From satisfaction of `Stp` it concludes only the propositional truncation of the corresponding `Under` comparison.
<!--zh-->
步进公式的向外充分性读式相对于序数载体 `d`、表 `f` 与两个被比较对象陈述。它对表的假设是：在 `d` 处记录的每个取值 `r` 都实现层关系 `IsRel d r`。由 `Stp` 的满足只能推出相应 `Under` 比较的命题截断。
<!--ja-->
ステップ論理式の外向きの妥当性は、順序数の台 `d`、表 `f`、比較される二つの対象に相対して述べられます。表についての仮定は、`d` で記録された各値 `r` が段階の関係 `IsRel d r` を実現するというものです。`Stp` の充足から得られるのは、対応する `Under` の比較の命題的切り詰めだけです。
<!--/-->

```agda
StpOut StpIn : StpFo → Type (ℓ-suc ℓ)
StpOut Stp = ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
           → ((r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
              → IsRel (fst (lookup d γ)) r)
           → ⟨ γ ⊨ Stp d f u v ⟩
```

<!--en-->
The outward direction deliberately returns `∥ Under ... ∥₁`, so it supplies existence of a local comparison without selecting a canonical witness. The inward direction has different input: the caller provides one particular value `r`, evidence that the table records it at `d`, and a proof that `r` realizes the relation there.
<!--zh-->
向外方向有意返回 `∥ Under ... ∥₁`，所以它只给出局部比较的存在，而不选择规范见证。向内方向的输入不同：调用方给出一个特定取值 `r`、表在 `d` 处记录它的证据，以及 `r` 实现当地关系的证明。
<!--ja-->
外向きは意図的に `∥ Under ... ∥₁` を返すので、局所的な比較の存在だけを与え、標準的な証人を選びません。内向きの入力は異なります。呼び出し側が一つの特定の値 `r` と、それが表の `d` で記録されている証拠、さらに `r` がそこでの関係を実現する証明を与えます。
<!--/-->

```agda
           → ∥ Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
                 (fst (lookup u γ)) (fst (lookup v γ)) ∥₁
StpIn Stp = ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
          → (r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
          → IsRel (fst (lookup d γ)) r
```

<!--en-->
The inward reading produces the formula satisfaction from the specific table entry and the `Under` comparison.
<!--zh-->
向内读法由特定表条目与 `Under` 比较产出公式满足。
<!--ja-->
内向きの読み出しが、特定の表の項目と `Under` の比較から、論理式の充足を作ります。
<!--/-->

```agda
          → Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
              (fst (lookup u γ)) (fst (lookup v γ))
          → ⟨ γ ⊨ Stp d f u v ⟩

```

<!--en-->
The module `Ordered` assumes an abstract step formula together with these two readings. Everything that follows is therefore a conditional translation of the birth-first rule: it proves the adequacy of the whole stage comparison from the adequacy of the same-birth comparison, without claiming here that any concrete step formula satisfies the interface.
<!--zh-->
模块 `Ordered` 假设一条抽象步进公式及其两条读式。因此，下文给出的是诞生层优先规则的有条件翻译：它从同生比较的充分性推出整个层比较的充分性，却不在本章声称任何具体步进公式已经满足该接口。
<!--ja-->
モジュール `Ordered` は、抽象的なステップ論理式と、この二つの読みを仮定します。したがって以下で得られるのは、誕生段階優先の規則の条件つき翻訳です。同じ誕生段階での比較の妥当性から段階全体の比較の妥当性を導きますが、具体的なステップ論理式がこのインターフェースを満たすことは、この章では主張しません。
<!--/-->

```agda
module Ordered (Stp : StpFo) (stp-out : StpOut Stp) (stp-in : StpIn Stp) where

```

<!--en-->
The four newly bound objects are the compared sets `u,v` and their candidate birth ordinals `du,dv`. The first two clauses assert `BirthAt du u` and `BirthAt dv v`; at this point those clauses identify births only when the later reading supplies ordinality of `du` and `dv`.
<!--zh-->
新绑定的四个对象是被比较集合 `u,v` 及其候选诞生序数 `du,dv`。前两项断言 `BirthAt du u` 与 `BirthAt dv v`；只有后续读式提供 `du`、`dv` 的序数性时，这两项才把候选者认同为相应诞生层。
<!--ja-->
新たに束縛される四つの対象は、比較される集合 `u,v` と、その誕生順序数の候補 `du,dv` です。最初の二つの条項は `BirthAt du u` と `BirthAt dv v` を主張します。これらが候補を実際の誕生段階と同一視するのは、後の読みが `du` と `dv` の順序数性を与えたときです。
<!--/-->

```agda
  OrdBody : ∀ {n} → Term S n → Fin n → Formula S (suc (suc (suc (suc n))))
  OrdBody tb f =
      BirthAt (suc zero) (sh3 zero)
    ∧̇ ( BirthAt zero (sh2 zero)
      ∧̇ ( (var (suc zero) ∈̇ tm4 tb)
```

<!--en-->
The next two clauses require both candidate births to belong to the stage denoted by `tb`. The final disjunction reproduces the birth-first rule: either `du ∈ dv`, or `dv ≡ du` and the supplied step formula compares `u` with `v` at that common carrier. No object-membership relation between `u` and `v` is asserted here.
<!--zh-->
接下来的两项要求两个候选诞生层都属于词项 `tb` 所指称的阶段。最后的析取复现诞生层优先规则：要么 `du ∈ dv`，要么 `dv ≡ du` 且外部给出的步进公式在这个共同载体处比较 `u` 与 `v`。这里没有断言 `u` 与 `v` 之间的集合隶属关系。
<!--ja-->
次の二つの条項は、誕生段階の二つの候補がともに項 `tb` の表す段階に属することを要求します。最後の選言は誕生段階優先の規則を再現します。すなわち、`du ∈ dv` であるか、または `dv ≡ du` であり、与えられたステップ論理式がその共通の台で `u` と `v` を比較します。ここでは `u` と `v` の間の集合所属を主張していません。
<!--/-->

```agda
        ∧̇ ( (var zero ∈̇ tm4 tb)
          ∧̇ ( (var (suc zero) ∈̇ var zero)
            ∨̇ ( (var zero ≐ var (suc zero))
              ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ) ) )
```

<!--en-->
`CondCore` first existentially binds the two compared objects `u` and `v`. The pair formula requires the argument in slot `z` to be their ordered pair. Two further existential quantifiers bind their candidate births before `OrdBody` checks the birth-first comparison. All four witnesses occur under the satisfaction semantics of existential formulas and are therefore propositionally truncated.
<!--zh-->
`CondCore` 先以存在量词绑定两个被比较对象 `u` 与 `v`，对公式要求槽位 `z` 中的实参是二者的有序对。随后两个存在量词绑定它们的候选诞生层，再由 `OrdBody` 检查诞生层优先的比较。四个见证都位于存在公式的满足语义下，因此都经过命题截断。
<!--ja-->
`CondCore` はまず、比較される二つの対象 `u` と `v` を存在量化します。対を表す論理式は、スロット `z` の引数がそれらの順序対であることを要求します。さらに二つの存在量化が誕生段階の候補を束縛し、その後で `OrdBody` が誕生段階優先の比較を調べます。四つの証人はいずれも存在論理式の充足意味論のもとにあるため、命題的に切り詰められています。
<!--/-->

```agda
  opaque
    CondCore : ∀ {n} → Fin n → Term S n → Fin n → Formula S n
    CondCore z tb f =
      ∃̇ ( ∃̇ ( prAtL (sh2 z) (suc zero) zero ∧̇ ∃̇ (∃̇ (OrdBody tb f)) ) )
```

<!--en-->
## What the description says, both ways
<!--zh-->
## 这条描述说了什么，两个方向
<!--ja-->
## 記述の意味を双方向に読む
<!--/-->

<!--en-->
To read `CondCore`, fix the ordinal stage denoted by `tb` and a table over that stage. `Values` guarantees that every recorded value realizes the appropriate local relation, while `Entries` says merely that some value is recorded at every carrier below the stage. These are exactly the hypotheses later used in the two directions.
<!--zh-->
为读取 `CondCore`，固定由 `tb` 指称的序数阶段及其上的一张表。`Values` 保证每个已记录取值都实现相应的局部关系；`Entries` 则只说阶段以下每个载体处都记录着某个取值。这正是后面两个方向所用的假设。
<!--ja-->
`CondCore` を読むため、`tb` が表す順序数段階と、その段階上の表を固定します。`Values` は記録された各値が対応する局所関係を実現することを保証し、`Entries` は段階より下の各台で何らかの値が記録されていることだけを述べます。これらが、後の二方向で使う仮定です。
<!--/-->

```agda
  module _ {n : ℕ} (z : Fin n) (tb : Term S n) (f : Fin n) (γ : S ^ n)
           (oα : IsOrd (fst (⟦ tb ⟧ γ)))
           (vals : Values (lookup f γ) (fst (⟦ tb ⟧ γ)))
           (ents : Entries (lookup f γ) (fst (⟦ tb ⟧ γ))) where
    private
```

<!--en-->
The stage ordinal is named for direct reference.
<!--zh-->
阶段序数被命名以便直接引用。
<!--ja-->
段階の順序数が、直接参照のために名づけられます。
<!--/-->

```agda
      α : V ℓ
      α = fst (⟦ tb ⟧ γ)

```

<!--en-->
The shifting lemma confirms that the four-slot renaming preserves the denotation of the stage term.
<!--zh-->
平移引理确认四槽改名保持阶段词项的指称。
<!--ja-->
ずらしの補題が、四つの枠の改名が段階の項の表示を保つことを確認します。
<!--/-->

```agda
      shift : (u v du dv : S) → ⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ) ≡ ⟦ tb ⟧ γ
      shift u v du dv = tm4-val tb u v du dv γ

```

<!--en-->
For a carrier `d` below `α`, `Entries` supplies only a propositionally truncated table value. The helper may eliminate that truncation into any proposition `P`: for each recovered `r`, `Values` proves `IsRel d r`, and the continuation uses the recorded pair together with that proof to establish `P`.
<!--zh-->
对 `α` 以下的载体 `d`，`Entries` 只给出一项经过命题截断的表取值。这个辅助引理可以把该截断消去到任意命题 `P` 中：对恢复出的每个 `r`，`Values` 证明 `IsRel d r`，续至函数再用已记录的有序对及这份证明得到 `P`。
<!--ja-->
`α` より下の台 `d` に対し、`Entries` が与える表の値は命題的に切り詰められています。この補助補題は、その切り詰めを任意の命題 `P` へ除去できます。得られた各 `r` について `Values` が `IsRel d r` を証明し、継続関数が記録された順序対とその証明を使って `P` を導きます。
<!--/-->

```agda
      value : (d : S) → ⟨ fst d ∈ α ⟩ → (P : hProp (ℓ-suc ℓ))
            → ((r : S) → ⟨ pr (fst d) (fst r) ∈ fst (lookup f γ) ⟩
               → IsRel (fst d) r → ⟨ P ⟩)
            → ⟨ P ⟩
      value d hd P k = PT.rec (snd P)
```

<!--en-->
Concretely, `ents d hd` gives the truncated pair consisting of a value `r` and its table entry. Propositional truncation is eliminated only because `P` is an `hProp`; `vals` then supplies the relation-realization proof required by the continuation. The construction does not select a table value outside that proposition.
<!--zh-->
具体地说，`ents d hd` 给出由取值 `r` 及其表条目组成的命题截断。这里只因 `P` 是 `hProp` 才能消去命题截断；随后 `vals` 提供续至函数所需的关系实现证明。该构造不会在这个命题之外选定一个表取值。
<!--ja-->
具体的には、`ents d hd` は値 `r` とその表項目からなる命題的切り詰めを与えます。ここで切り詰めを除去できるのは `P` が `hProp` だからであり、その後 `vals` が継続関数に必要な関係の実現証明を与えます。この構成は、その命題の外で表の値を選びません。
<!--/-->

```agda
        (λ { (r , hr) → k r hr (vals d r hd hr) }) (ents d hd)

```

<!--en-->
The deep satisfaction type reads the ordered body at the four-slot environment built from the two comparison objects and their birth ordinals.
<!--zh-->
深层满足类型读取有序体在由两个比较对象及其诞生序数组成的四槽环境处的满足。
<!--ja-->
深い充足の型が、比較の二つの対象と、それらの誕生の順序数から作られた四つの枠の環境で、順序づけられた本体を読みます。
<!--/-->

```agda
      Deep : (u v du : S) → S → Type (ℓ-suc ℓ)
      Deep u v du dv = ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ OrdBody tb f ⟩

```

<!--en-->
The two readings use the same defining equation of `CondCore` in opposite directions. Outward, the four existential bindings are decoded into a pair and two birth candidates; inward, an existing `Related` comparison supplies those bindings. The equal-birth branch is the only point where the assumed readings of `Stp` enter.
<!--zh-->
两条读式以相反方向使用 `CondCore` 的同一个定义方程。向外时，四个存在绑定被读成一对成员及两个候选诞生层；向内时，一项已有的 `Related` 比较提供这些绑定。只有同生分支会用到对 `Stp` 的两条假设读式。
<!--ja-->
二つの読みは、`CondCore` の同じ定義方程式を逆向きに使います。外向きには、四つの存在束縛を一対の要素と二つの誕生段階の候補として読みます。内向きには、すでにある `Related` の比較からそれらの束縛を与えます。`Stp` について仮定した読みを使うのは、誕生段階が等しい枝だけです。
<!--/-->

```agda
    opaque
     unfolding CondCore

```

<!--en-->
The outward reading opens the four nested existential witnesses in order: the compared objects `u,v`, then their candidate births `du,dv`. Each witness is available only through propositional truncation, and each elimination targets `Related α ...`, which is a proposition. The innermost data is then passed to the mathematical comparison argument.
<!--zh-->
向外读式依次打开四层存在见证：先是被比较对象 `u,v`，再是候选诞生层 `du,dv`。每个见证都只能通过命题截断取得，而每次消去的目标都是命题 `Related α ...`。最内层数据随后交给数学比较论证。
<!--ja-->
外向きの読みは、入れ子になった四つの存在証人を順に開きます。まず比較される対象 `u,v`、次に誕生段階の候補 `du,dv` です。各証人は命題的切り詰めを通してのみ得られ、どの除去も命題 `Related α ...` を目標とします。最も内側のデータは、その後で数学的な比較の議論へ渡されます。
<!--/-->

```agda
     CondCore-out : ⟨ γ ⊨ CondCore z tb f ⟩ → ⟨ Related α (fst (lookup z γ)) ⟩
     CondCore-out = PT.rec (snd (Related α (fst (lookup z γ))))
       (λ { (u , hv) → PT.rec (snd (Related α (fst (lookup z γ))))
         (λ { (v , (hp , hdu)) → PT.rec (snd (Related α (fst (lookup z γ))))
           (λ { (du , hdv) → PT.rec (snd (Related α (fst (lookup z γ))))
```

<!--en-->
The local name `Goal` records the proposition that the argument in slot `z` satisfies the meta-level predicate `Related α`. The pair equation and the satisfaction of `OrdBody` for the four recovered witnesses are the two ingredients passed to `atDeep`; the remaining proof will turn them into that relatedness proposition.
<!--zh-->
局部名称 `Goal` 记录这样一个命题：槽位 `z` 中的实参满足元语言谓词 `Related α`。恢复出的四个见证给出有序对等式与 `OrdBody` 的满足，这两项被交给 `atDeep`；余下证明将把它们转化为该关联命题。
<!--ja-->
局所名 `Goal` は、スロット `z` の引数がメタ言語の述語 `Related α` を満たすという命題を表します。復元された四つの証人から、順序対の等式と `OrdBody` の充足が得られ、この二つが `atDeep` に渡されます。残りの証明は、それらをこの関係づけの命題へ変換します。
<!--/-->

```agda
             (λ { (dv , hd) → atDeep u v du dv hp hd }) hdv }) hdu }) hv })
       where
       Goal : Type (ℓ-suc ℓ)
       Goal = ⟨ Related α (fst (lookup z γ)) ⟩

```

<!--en-->
After the four existential witnesses have been opened into the proposition `Related`, the outward proof has two pieces of information: `hp` says that the argument is the coded pair of `u` and `v`, while the deep record says that `du,dv` are candidate births below the ambient stage and satisfy the birth-first comparison. The witnesses are used only inside this propositional target; the proof does not select a canonical pair or canonical birth data.
<!--zh-->
四个存在见证被消去到命题 `Related` 之后，向外证明取得两部分信息：`hp` 说明实参是 `u` 与 `v` 的编码有序对；深层记录则说明 `du,dv` 是环境层以下的候选诞生层，并满足诞生层优先的比较。这些见证只在命题目标中使用；证明并未选出规范的有序对或规范的诞生数据。
<!--ja-->
四つの存在証人を命題 `Related` へ除去すると、外向きの証明には二種類の情報が残ります。`hp` は引数が `u` と `v` の符号化された順序対であることを述べ、深い記録は `du,dv` が周囲の段階より下にある誕生段階の候補で、誕生段階優先の比較を満たすことを述べます。これらの証人は命題である目標の中だけで使われ、標準的な対や誕生データが選ばれるわけではありません。
<!--/-->

```agda
       atDeep : (u v du dv : S)
              → ⟨ (v ∷ u ∷ γ) ⊨ prAtL (sh2 z) (suc zero) zero ⟩
              → Deep u v du dv → Goal
       atDeep u v du dv hp (hbu , (hbv , (hmu₀ , (hmv₀ , hcmp)))) =
         subst (λ w → ⟨ Related α w ⟩) (sym qz)
```

<!--en-->
Adequacy of the pairing formula identifies the set in slot `z` with `pr (fst u) (fst v)`. It is this equality, rather than an equality between `u` and `v`, that lets the proof change its target to `Related α` of the represented pair and analyze the birth comparison there.
<!--zh-->
配对公式的充分性把槽位 `z` 中的集合认同为 `pr (fst u) (fst v)`。正是这条等式，而非 `u` 与 `v` 之间的等式，使证明能把目标改写为该表示对的 `Related α`，再分析其中的诞生层比较。
<!--ja-->
対を表す論理式の妥当性により、スロット `z` の集合は `pr (fst u) (fst v)` と同一視されます。これは `u` と `v` の等式ではありません。この等式によって目標を、表された対についての `Related α` に書き換え、そこで誕生段階の比較を分析できます。
<!--/-->

```agda
           (PT.rec (snd (Related α (pr (fst u) (fst v)))) atCase hcmp)
         where
         qz : fst (lookup z γ) ≡ pr (fst u) (fst v)
         qz = subst ⟨_⟩ (prAtL-adequate (sh2 z) (suc zero) zero (v ∷ u ∷ γ)) hp

```

<!--en-->
The membership of the first birth stage in the ordinal is transported along the shift of environments: the shifted and unshifted readings of the birth stage agree on the underlying set.
<!--zh-->
第一个诞生层在序数中的隶属沿环境移位搬运：诞生层的移位读法与非移位读法在底层集合上一致。
<!--ja-->
第一の誕生段階の順序数への所属は、環境のずらしに沿って運ばれます。誕生段階のずらした読みとずらさない読みは、底の集合について一致するのです。
<!--/-->

```agda
         hmu : ⟨ fst du ∈ α ⟩
         hmu = subst (λ w → ⟨ fst du ∈ fst w ⟩) (shift u v du dv) hmu₀

```

<!--en-->
The second birth stage is transported by the same shift, so both birth stages are known to belong to the ordinal.
<!--zh-->
第二个诞生层由同一移位搬运，于是两个诞生层都属于该序数。
<!--ja-->
第二の誕生段階も同じずらしで運ばれ、こうして二つの誕生段階とも順序数の中にあることが分かります。
<!--/-->

```agda
         hmv : ⟨ fst dv ∈ α ⟩
         hmv = subst (λ w → ⟨ fst dv ∈ fst w ⟩) (shift u v du dv) hmv₀

```

<!--en-->
The first birth stage is an ordinal: it belongs to the ordinal, and members of ordinals are ordinals.
<!--zh-->
第一个诞生层是序数：它属于该序数，而序数的成员是序数。
<!--ja-->
第一の誕生段階は順序数です。順序数の中にあり、順序数の要素は順序数だからです。
<!--/-->

```agda
         odu : IsOrd (fst du)
         odu = mem-ord {A = α} oα (fst du) hmu

```

<!--en-->
The second birth stage is an ordinal by the same argument.
<!--zh-->
第二个诞生层由同样论证是序数。
<!--ja-->
第二の誕生段階も同じ議論で順序数になります。
<!--/-->

```agda
         odv : IsOrd (fst dv)
         odv = mem-ord {A = α} oα (fst dv) hmv

```

<!--en-->
The reading lemma of the birth formula now applies to the first birth stage: with its ordinalness, the satisfaction of the birth formula identifies the recorded stage with the true birth ordinal of the first object.
<!--zh-->
诞生公式的读取引理现在适用于第一个诞生层：在其序数性下，诞生公式的满足把被记录的层认同为第一个对象的真正诞生序数。
<!--ja-->
誕生の論理式の読みの補題が、第一の誕生段階に適用されます。その順序数性のもとで、誕生の論理式の充足が、記録された段階を、最初の対象の本当の誕生順序数と同一視するのです。
<!--/-->

```agda
         qu : fst du ≡ birth (fst u) (snd u)
         qu = BirthAt-out (suc zero) (sh3 zero) ((dv ∷ du ∷ v ∷ u ∷ γ)) hbu odu

```

<!--en-->
The same reading applies to the second birth stage and the second object.
<!--zh-->
同样的读取适用于第二个诞生层与第二个对象。
<!--ja-->
同じ読みが、第二の誕生段階と第二の対象に適用されます。
<!--/-->

```agda
         qv : fst dv ≡ birth (fst v) (snd v)
         qv = BirthAt-out zero (sh2 zero) ((dv ∷ du ∷ v ∷ u ∷ γ)) hbv odv

```

<!--en-->
The first object can now be regarded as a member of `Lset α`. Its constructibility evidence is already carried by `u`; the new fact is membership in the ambient level, obtained from `bornIn` because the identified birth ordinal belongs to `α`.
<!--zh-->
现在可以把第一个对象视为 `Lset α` 的成员。其可构造性证据已由 `u` 携带；新增的事实是它属于环境层，而这由 `bornIn` 从「已经认出的诞生序数属于 `α`」推出。
<!--ja-->
これで最初の対象を `Lset α` の要素とみなせます。構成可能性の証拠はすでに `u` が持っており、新たに得るのは周囲の段階への所属です。これは、同定された誕生順序数が `α` に属することから `bornIn` によって従います。
<!--/-->

```agda
         a : Mem (Lset α)
         a = fst u , bornIn α oα (fst u) (snd u)
               (subst (λ w → ⟨ w ∈ α ⟩) qu hmu)

```

<!--en-->
The second object is packaged identically.
<!--zh-->
第二个对象以同样方式打包。
<!--ja-->
第二の対象も同じようにまとめられます。
<!--/-->

```agda
         c : Mem (Lset α)
         c = fst v , bornIn α oα (fst v) (snd v)
               (subst (λ w → ⟨ w ∈ α ⟩) qv hmv)

```

<!--en-->
The packaged member `a` carries the same underlying set as `u`, although its constructibility proof was obtained through stage membership. Proof irrelevance for that evidence, expressed by `birth-proof`, shows that its computed birth agrees with the birth computed from `u`; composing with `qu` identifies it with the recorded stage `du`.
<!--zh-->
打包成员 `a` 与 `u` 有相同的底层集合，但其可构造性证明来自层隶属。`birth-proof` 表达这份证据的证明无关性，说明从 `a` 算出的诞生层与从 `u` 算出的诞生层相同；再与 `qu` 复合，便把它认同为记录的层 `du`。
<!--ja-->
まとめられた要素 `a` と `u` の底の集合は同じですが、`a` の構成可能性の証明は段階への所属から得られています。`birth-proof` はこの証拠についての証明無関係性を表し、`a` から計算した誕生と `u` から計算した誕生が一致することを示します。さらに `qu` と合成すると、記録された段階 `du` と同一視できます。
<!--/-->

```agda
         qa : bornOf α oα a ≡ fst du
         qa = birth-proof (fst u) (memberL α oα a) (snd u) ∙ sym qu

```

<!--en-->
The birth ordinal of the packaged second object agrees with the recorded second birth stage.
<!--zh-->
打包后的第二个对象的诞生序数与被记录的第二个诞生层一致。
<!--ja-->
まとめられた第二の対象の誕生順序数は、記録された第二の誕生段階と一致します。
<!--/-->

```agda
         qc : bornOf α oα c ≡ fst dv
         qc = birth-proof (fst v) (memberL α oα c) (snd v) ∙ sym qv

```

<!--en-->
It remains to prove the meta-language comparison `relOf (orderAt α oα) a c`. The order-table interface then maps that comparison to the proposition that the coded pair of the two underlying sets belongs to `Related α`. No object-language relation has yet been chosen at this step.
<!--zh-->
此时只需证明元语言比较 `relOf (orderAt α oα) a c`。序表接口随后把这项比较送到命题：两个底层集合的编码有序对属于 `Related α`。这一步尚未选取任何对象语言关系集合。
<!--ja-->
残る目標は、メタ言語での比較 `relOf (orderAt α oα) a c` を示すことです。順序表のインターフェースは、その比較を、二つの底の集合の符号化された順序対が `Related α` に属するという命題へ移します。この段階で対象言語の関係集合を選んでいるわけではありません。
<!--/-->

```agda
         fill : relOf (orderAt α oα) a c → ⟨ Related α (pr (fst u) (fst v)) ⟩
         fill = related-in α oα a c

```

<!--en-->
The comparison encoded by `OrdBody` has exactly the two branches in the one-step unfolding of `orderAt`. If `du ∈ dv`, the identifications `qa` and `qc` turn this into the earlier-birth branch for `a` and `c`; transporting through `order-unfold` then gives their stage-order comparison.
<!--zh-->
`OrdBody` 编码的比较恰有 `orderAt` 一次展开所得的两支。若 `du ∈ dv`，同一视 `qa` 与 `qc` 把它改写成 `a` 与 `c` 的「诞生更早」分支；沿 `order-unfold` 搬运后，即得二者的层序比较。
<!--ja-->
`OrdBody` が符号化する比較には、`orderAt` を一段開いたときと同じ二つの枝があります。`du ∈ dv` の場合、`qa` と `qc` によって、これは `a` と `c` の「誕生がより早い」枝へ書き換えられます。さらに `order-unfold` に沿って輸送すると、両者の段階順序での比較が得られます。
<!--/-->

```agda
         atCase : ⟨ fst du ∈ fst dv ⟩
                ⊎ ( (fst dv ≡ fst du)
                  × ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ⟩ )
                → ⟨ Related α (pr (fst u) (fst v)) ⟩
         atCase (inl h) = fill (transport (sym (order-unfold α oα a c))
```

<!--en-->
In the equal-birth branch, `OrdBody` supplies satisfaction of the abstract formula `Stp`. Applying `stp-out` with the ordinality of the common birth and the `Values` hypothesis yields only a propositionally truncated `Under` comparison. That truncation may be eliminated into `Related`, which is a proposition; the argument neither inspects how `Stp` obtained a table value nor extracts such a value.
<!--zh-->
在同生分支中，`OrdBody` 给出抽象公式 `Stp` 的满足。把公共诞生层的序数性与 `Values` 假设交给 `stp-out`，只能得到一项经过命题截断的 `Under` 比较。由于 `Related` 是命题，可以把这项截断消去到其中；该论证既不考察 `Stp` 如何取得表值，也不从中提取表值。
<!--ja-->
誕生段階が等しい枝では、`OrdBody` から抽象的な論理式 `Stp` の充足が得られます。共通の誕生段階の順序数性と `Values` の仮定を `stp-out` に渡すと、命題的に切り詰められた `Under` の比較だけが得られます。`Related` は命題なので、この切り詰めをそこへ除去できます。この議論は、`Stp` が表の値をどのように得たかを調べず、その値を取り出すこともありません。
<!--/-->

```agda
           (inl (subst2 (λ p q → ⟨ p ∈ q ⟩) (sym qa) (sym qc) h)))
         atCase (inr (e , hs)) = PT.rec
           (snd (Related α (pr (fst u) (fst v)))) atUnder
           (stp-out (suc zero) (sh4 f) (sh3 zero) (sh2 zero)
             ((dv ∷ du ∷ v ∷ u ∷ γ)) odu (λ r hr → vals du r hmu hr) hs)
```

<!--en-->
Given an `Under` comparison at the recorded common birth, the proof must align it with the birth attached to the packaged member `a`. Once aligned, it supplies the equal-birth branch of `order-unfold`; the resulting `orderAt` comparison is then represented by `Related`.
<!--zh-->
给定记录的公共诞生层处的一项 `Under` 比较，证明还须把它与打包成员 `a` 所带的诞生层对齐。对齐之后，它给出 `order-unfold` 的同生分支；所得 `orderAt` 比较再由 `Related` 表示。
<!--ja-->
記録された共通の誕生段階での `Under` の比較が与えられたら、それを、まとめられた要素 `a` に付随する誕生段階とそろえる必要があります。そろえた比較は `order-unfold` の同じ誕生の枝を与え、得られた `orderAt` の比較が `Related` によって表されます。
<!--/-->

```agda
           where
           atUnder : Under (fst du) (stepOrder (fst du) odu) (fst u) (fst v)
                   → ⟨ Related α (pr (fst u) (fst v)) ⟩
           atUnder und = fill (transport (sym (order-unfold α oα a c))
             (inr (qc ∙ e ∙ sym qa
```

<!--en-->
The alignment uses the equality `qa` between the two carrier ordinals. `stepMoved` transports the local comparison along this equality and reconciles the two ordinalness proofs by proof irrelevance. It does not use transitivity of the shared ordinal and does not create a new local order.
<!--zh-->
这次对齐使用两条载体序数之间的等式 `qa`。`stepMoved` 沿该等式搬运局部比较，并借助证明无关性认同两份序数性证明；这里既不使用公共序数的传递性，也不构造新的局部序。
<!--ja-->
この整合には、二つの台となる順序数の等式 `qa` を使います。`stepMoved` はこの等式に沿って局所比較を輸送し、証明無関係性によって二つの順序数性の証明を一致させます。共通の順序数の推移性を使ったり、新しい局所順序を作ったりはしません。
<!--/-->

```agda
               , stepMoved (fst du) (bornOf α oα a) (sym qa) odu
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a))
                   (fst u) (fst v) und)))

```

<!--en-->
For the inward direction, `Related α z` contains an ordinalness proof and, under propositional truncation, two members `a,c` of `Lset α`, an equation saying that `z` is their coded pair, and their `Ordering` comparison. `Pairs` names precisely this payload so that it can be eliminated only into the satisfaction proposition being constructed.
<!--zh-->
在向内方向，`Related α z` 包含一份序数性证明，以及命题截断下的如下数据：`Lset α` 的两个成员 `a,c`、说明 `z` 是二者编码有序对的等式，以及二者的 `Ordering` 比较。`Pairs` 恰为这份载荷取名，使它只能被消去到正在构造的满足命题中。
<!--ja-->
内向きでは、`Related α z` は順序数性の証明と、命題的切り詰めのもとに置かれた次のデータを含みます。`Lset α` の二つの要素 `a,c`、`z` がそれらの符号化された順序対であるという等式、そして両者の `Ordering` による比較です。`Pairs` はこのペイロードに名前を付け、構成中の充足命題への除去だけを行えるようにします。
<!--/-->

```agda
     private
       Pairs : IsOrd α → Type (ℓ-suc ℓ)
       Pairs o = Σ[ a ∈ Mem (Lset α) ] ∥ (Σ[ c ∈ Mem (Lset α) ]
         ( (fst (lookup z γ) ≡ pr (fst a) (fst c)) × ⟨ Ordering α o a c ⟩ )) ∥₁

```

<!--en-->
The inward reading eliminates the truncated contents of `Related` into satisfaction of `CondCore`. Once an ordinalness proof and a represented pair are available locally, `atRel` reconstructs the four existential witnesses and the birth-first comparison; no global choice of a represented pair is produced.
<!--zh-->
向内读式把 `Related` 的截断内容消去到 `CondCore` 的满足命题中。局部取得序数性证明与一对被表示的成员后，`atRel` 重建四个存在见证及诞生层优先比较；证明不会产出对表示成员的全局选择。
<!--ja-->
内向きの読みは、`Related` の切り詰められた内容を `CondCore` の充足へ除去します。順序数性の証明と表された要素の対が局所的に得られると、`atRel` が四つの存在証人と誕生段階優先の比較を組み立てます。表す要素の対を大域的に選ぶものではありません。
<!--/-->

```agda
     CondCore-in : ⟨ Related α (fst (lookup z γ)) ⟩ → ⟨ γ ⊨ CondCore z tb f ⟩
     CondCore-in = PT.rec (snd (γ ⊨ CondCore z tb f)) atOrd
       where
       atRel : (o : IsOrd α) (a c : Mem (Lset α))
             → fst (lookup z γ) ≡ pr (fst a) (fst c)
```

<!--en-->
The ambient ordinalness `oα` is already a hypothesis of the whole reading. Here the local proof instead extracts the constructibility component `pα` from the value of the stage term, then asks the table for a value at the first member's birth. Because the target is a satisfaction proposition, the merely existing table value can be eliminated into it.
<!--zh-->
环境序数性 `oα` 已是整条读式的假设。此处的局部证明从层词项的取值中取出的是可构造性分量 `pα`，随后向表索取第一个成员诞生层处的一个取值。由于目标是满足命题，表值的仅仅存在可以消去到其中。
<!--ja-->
周囲の順序数性 `oα` は、読み全体の仮定としてすでに与えられています。ここで局所的に取り出すのは、段階を表す項の値がもつ構成可能性の成分 `pα` です。その後、最初の要素の誕生段階における値を表に求めます。目標は充足という命題なので、表の値の単なる存在をそこへ除去できます。
<!--/-->

```agda
             → ⟨ Ordering α o a c ⟩ → ⟨ γ ⊨ CondCore z tb f ⟩
       atRel o a c q hord =
         value (bornS α oα pα a) hmu (γ ⊨ CondCore z tb f) atValue
         where
         pα : ⟨ isL α ⟩
```

<!--en-->
Every term is interpreted in the structure `𝒮ʟ`, whose elements pair an underlying set with evidence of constructibility. Thus the second projection of `⟦ tb ⟧ γ` supplies `isL α`; this is part of the semantic value of the term, rather than a separate satisfaction assumption.
<!--zh-->
每个词项都在结构 `𝒮ʟ` 中解释，而该结构的元素由底层集合及其可构造性证据组成。因此，`⟦ tb ⟧ γ` 的第二投影给出 `isL α`；这是词项语义值的一部分，并非另一项满足假设。
<!--ja-->
各項は構造 `𝒮ʟ` で解釈され、その要素は底の集合と、その構成可能性の証拠との組です。したがって `⟦ tb ⟧ γ` の第二射影が `isL α` を与えます。これは項の意味値の一部であり、別の充足仮定ではありません。
<!--/-->

```agda
         pα = snd (⟦ tb ⟧ γ)

```

<!--en-->
The witnesses for `CondCore` are now chosen locally: `u,v` package the two stage members as elements of `𝒮ʟ`, and `du,dv` package their actual birth ordinals. These are witnesses for this proof of a proposition, not canonical choices exported from `Related`.
<!--zh-->
现在局部给出 `CondCore` 的见证：`u,v` 把两个层成员封装为 `𝒮ʟ` 的元素，`du,dv` 则封装它们真正的诞生序数。它们只是这次命题证明所用的见证，并非从 `Related` 导出的规范选择。
<!--ja-->
ここで `CondCore` の証人を局所的に与えます。`u,v` は二つの段階要素を `𝒮ʟ` の要素としてまとめ、`du,dv` はそれぞれの実際の誕生順序数をまとめます。これらはこの命題の証明に使う証人であり、`Related` から取り出される標準的な選択ではありません。
<!--/-->

```agda
         u v du dv : S
         u = memS α oα a
         v = memS α oα c
         du = bornS α oα pα a
         dv = bornS α oα pα c
```

<!--en-->
For every member of `Lset α`, its true birth ordinal lies below `α`. Since the first projection of `bornS` is that ordinal, the same membership statement holds for the value placed in slot `du`; this is the form inspected by the object-language clause.
<!--zh-->
`Lset α` 的每个成员，其真正诞生序数都低于 `α`。由于 `bornS` 的第一投影就是该序数，同一隶属陈述也适用于放入槽位 `du` 的值；对象语言子句读取的正是这个形式。
<!--ja-->
`Lset α` の各要素について、その真の誕生順序数は `α` より下にあります。`bornS` の第一射影はその順序数なので、同じ所属の主張がスロット `du` に置かれた値についても成り立ちます。対象言語の条項が調べるのはこの形です。
<!--/-->

```agda

         hmu : ⟨ fst du ∈ α ⟩
         hmu = subst (λ w → ⟨ w ∈ α ⟩) (sym (bornS-fst α oα pα a))
           (bornMem α oα a)

```

<!--en-->
The birth stage of the second member belongs to the ordinal by the same transport.
<!--zh-->
第二个成员的诞生层经同样搬运属于该序数。
<!--ja-->
第二の要素の誕生段階も、同じ輸送によって順序数の中にあります。
<!--/-->

```agda
         hmv : ⟨ fst dv ∈ α ⟩
         hmv = subst (λ w → ⟨ w ∈ α ⟩) (sym (bornS-fst α oα pα c))
           (bornMem α oα c)

```

<!--en-->
The first birth stage is an ordinal, since it lies inside the ordinal.
<!--zh-->
第一个诞生层是序数，因为它落在该序数之内。
<!--ja-->
第一の誕生段階は順序数です。順序数の中にあるからです。
<!--/-->

```agda
         odu : IsOrd (fst du)
         odu = mem-ord {A = α} oα (fst du) hmu

```

<!--en-->
The second birth stage is an ordinal by the same reading.
<!--zh-->
第二个诞生层由同样读取是序数。
<!--ja-->
第二の誕生段階も、同じ読みによって順序数です。
<!--/-->

```agda
         odv : IsOrd (fst dv)
         odv = mem-ord {A = α} oα (fst dv) hmv

```

<!--en-->
Unfolding the already constructed stage order yields its two-branch lexicographic rule. Either `a` was born strictly before `c`, or their births agree and the local `stepOrder` at that common birth places the underlying set of `a` below that of `c`.
<!--zh-->
展开已经构造好的层序，得到其两分的字典序规则：要么 `a` 的诞生严格早于 `c`，要么二者诞生层相同，且该公共诞生层处的局部 `stepOrder` 把 `a` 的底层集合排在 `c` 的底层集合之前。
<!--ja-->
構成済みの段階順序を開くと、二つの枝からなる辞書式の規則が得られます。`a` が `c` より真に早く生まれたか、または両者の誕生が一致し、その共通の誕生段階での局所的な `stepOrder` が `a` の底の集合を `c` の底の集合より前に置くかです。
<!--/-->

```agda
         cmp : ⟨ bornOf α oα a ∈ bornOf α oα c ⟩
             ⊎ ( (bornOf α oα c ≡ bornOf α oα a)
               × Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                   (fst a) (fst c) )
```

<!--en-->
The comparison is obtained by transporting the strict reading along the identification of the two ordinalness proofs, since ordinalness is a proposition and the two proofs describe the same ordinal.
<!--zh-->
该比较沿「两份序数性证明的同一视」搬运严格读法而得，因为序数性是命题，两份证明描述的是同一个序数。
<!--ja-->
比較は、二つの順序数性の証明の同一視に沿って、狭義の読みを運ぶことで得られます。順序数性は命題であり、二つの証明は同じ順序数を記述するからです。
<!--/-->

```agda
         cmp = transport (order-unfold α oα a c)
           (strict α oα a c (subst (λ o' → ⟨ Ordering α o' a c ⟩)
             (isPropIsOrd α o oα) hord))

```

<!--en-->
The equation contained in `Related` identifies the argument with the ordered pair of the underlying sets of `a` and `c`. The first-projection equations for `memS` rewrite those endpoints as the values placed in slots `u` and `v`, giving exactly the pairing clause required by `CondCore`.
<!--zh-->
`Related` 所含的等式把实参认同为 `a` 与 `c` 的底层集合所成的有序对。`memS` 的第一投影等式把这两个端点改写为放入槽位 `u` 与 `v` 的值，从而恰好得到 `CondCore` 所需的配对子句。
<!--ja-->
`Related` に含まれる等式は、引数を `a` と `c` の底の集合からなる順序対と同一視します。`memS` の第一射影の等式によって、その二つの端点をスロット `u` と `v` に置かれた値へ書き換えると、`CondCore` が要求する対の条項がちょうど得られます。
<!--/-->

```agda
         hp : ⟨ (v ∷ u ∷ γ) ⊨ prAtL (sh2 z) (suc zero) zero ⟩
         hp = subst ⟨_⟩
           (sym (prAtL-adequate (sh2 z) (suc zero) zero (v ∷ u ∷ γ)))
           (q ∙ cong₂ pr (sym (memS-fst α oα a)) (sym (memS-fst α oα c)))

```

<!--en-->
To fill the first `BirthAt` clause, the inward reading supplies both facts that its adequacy lemma requires: `du` is ordinal, and its underlying set is exactly the birth ordinal of `u`. The formula itself still does not assert ordinality or choose a least stage.
<!--zh-->
为填入第一条 `BirthAt` 子句，向内读式给出其充分性引理所需的两项事实：`du` 是序数，且其底层集合恰是 `u` 的诞生序数。公式本身仍不断言序数性，也不选择最小层。
<!--ja-->
最初の `BirthAt` の条項を満たすため、内向きの読みは妥当性補題が必要とする二つの事実を与えます。`du` が順序数であることと、その底の集合がちょうど `u` の誕生順序数であることです。論理式それ自体が順序数性を主張したり、最小の段階を選んだりするわけではありません。
<!--/-->

```agda
         hbu : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ BirthAt (suc zero) (sh3 zero) ⟩
         hbu = BirthAt-in (suc zero) (sh3 zero) (dv ∷ du ∷ v ∷ u ∷ γ) odu
           (bornS-birth α oα pα a)

```

<!--en-->
The birth formula for the second birth stage is filled at the same deep environment.
<!--zh-->
第二个诞生层的诞生公式在同一深环境中填充。
<!--ja-->
第二の誕生段階の誕生の論理式も、同じ深い環境のもとで埋められます。
<!--/-->

```agda
         hbv : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ BirthAt zero (sh2 zero) ⟩
         hbv = BirthAt-in zero (sh2 zero) (dv ∷ du ∷ v ∷ u ∷ γ) odv
           (bornS-birth α oα pα c)

```

<!--en-->
In the equal-birth branch, `cmp` supplies an `Under` comparison on the actual birth carrier of `a` and on the underlying sets of `a,c`. The step formula, however, is read at the packaged values `du,u,v`, so the carrier and both endpoints must be transported to those representations.
<!--zh-->
在同生分支中，`cmp` 给出一项 `Under` 比较，其载体是 `a` 的真正诞生层，两个端点是 `a,c` 的底层集合。但步进公式读在封装值 `du,u,v` 上，因此必须把载体与两个端点都搬到这些表示中。
<!--ja-->
誕生が等しい枝では、`cmp` から、`a` の実際の誕生段階を台とし、`a,c` の底の集合を端点とする `Under` の比較が得られます。一方、ステップ論理式はまとめられた値 `du,u,v` で読まれるため、台と二つの端点をそれらの表現へ輸送する必要があります。
<!--/-->

```agda
         moved : Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                   (fst a) (fst c)
               → Under (fst du) (stepOrder (fst du) odu) (fst u) (fst v)
         moved und = subst2 (λ p r → Under (fst du) (stepOrder (fst du) odu) p r)
```

<!--en-->
The endpoint transports use the exposed underlying-set equations for `memS`. The carrier transport uses `bornS-fst` and `stepMoved`, whose dependent path also identifies the two proofs of ordinality because `IsOrd` is a proposition. No transitivity argument is involved.
<!--zh-->
两个端点的搬运使用 `memS` 的底层集合外显等式。载体的搬运使用 `bornS-fst` 与 `stepMoved`；后者的依赖路径还利用 `IsOrd` 是命题来认同两份序数性证明。这里不涉及传递性论证。
<!--ja-->
二つの端点の輸送には、`memS` の底の集合について公開された等式を使います。台の輸送には `bornS-fst` と `stepMoved` を使い、その依存パスは `IsOrd` が命題であることから二つの順序数性の証明も同一視します。ここで推移性は使いません。
<!--/-->

```agda
           (sym (memS-fst α oα a)) (sym (memS-fst α oα c))
           (stepMoved (bornOf α oα a) (fst du) (sym (bornS-fst α oα pα a))
             (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)) odu
             (fst a) (fst c) und)

```

<!--en-->
`Entries` provides a merely existing table value `r` at the first birth, and `Values` proves that any such recorded value realizes `IsRel`. For each local payload, `atValue` constructs satisfaction of `CondCore` by inserting the two members and their two births. The table value is passed specifically to `stp-in` in the equal-birth branch; it is not made into a globally chosen value.
<!--zh-->
`Entries` 在第一个诞生层处给出一个仅仅存在的表值 `r`，而 `Values` 证明任一这样的记录值都实现 `IsRel`。对每份局部载荷，`atValue` 插入两个成员及其两个诞生层，构造 `CondCore` 的满足。同生分支把该表值专门传给 `stp-in`；它不会成为全局选定的取值。
<!--ja-->
`Entries` は最初の誕生段階における表の値 `r` の単なる存在を与え、`Values` はそのように記録されたどの値も `IsRel` を実現すると示します。各局所ペイロードについて、`atValue` は二つの要素と二つの誕生段階を挿入し、`CondCore` の充足を構成します。同じ誕生の枝では、この表の値をその場で `stp-in` に渡しますが、大域的に選ばれた値にはしません。
<!--/-->

```agda
         atValue : (r : S) → ⟨ pr (fst du) (fst r) ∈ fst (lookup f γ) ⟩
                 → IsRel (fst du) r → ⟨ γ ⊨ CondCore z tb f ⟩
         atValue r hr hrel = ∣ u , ∣ v , (hp , ∣ du , ∣ dv
           , (hbu , (hbv , (hmu₀ , (hmv₀ , side)))) ∣₁ ∣₁) ∣₁ ∣₁
           where
```

<!--en-->
Inside `OrdBody`, four new binders lie in front of the original environment, so the stage term appears as `tm4 tb`. The shift equation proves that this raised term still denotes `α`; it therefore transports the known membership of the first birth into the exact form required by the object-language clause.
<!--zh-->
在 `OrdBody` 内，原环境之前增加了四个绑定，故层词项写成 `tm4 tb`。移位等式证明这个提升后的词项仍指称 `α`，于是把第一诞生层的已知隶属搬成对象语言子句所需的确切形式。
<!--ja-->
`OrdBody` の内部では、もとの環境の前に四つの束縛が加わるため、段階を表す項は `tm4 tb` となります。シフトの等式により、この持ち上げられた項も `α` を表すことが分かり、第一の誕生段階について既知の所属を対象言語の条項が要求する形へ輸送できます。
<!--/-->

```agda
           hmu₀ : ⟨ fst du ∈ fst (⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ)) ⟩
           hmu₀ = subst (λ w → ⟨ fst du ∈ fst w ⟩) (sym (shift u v du dv)) hmu

```

<!--en-->
The second birth stage is transported by the same shift equation.
<!--zh-->
第二个诞生层经同一移位等式搬运。
<!--ja-->
第二の誕生段階も、同じずらしの等式で運ばれます。
<!--/-->

```agda
           hmv₀ : ⟨ fst dv ∈ fst (⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ)) ⟩
           hmv₀ = subst (λ w → ⟨ fst dv ∈ fst w ⟩) (sym (shift u v du dv)) hmv
```

<!--en-->
The remaining clause must reproduce the same two branches obtained from `order-unfold`: earlier birth, or equal birth followed by the local step comparison. The helper keeps this case split inside the satisfaction proposition, where the witnesses and any truncated table entry may legitimately be used.
<!--zh-->
余下的子句必须复现 `order-unfold` 给出的同一两支：诞生更早，或诞生相同后采用局部步进比较。辅助函数把这次分情形保持在满足命题内部，使见证与任何截断的表项都只在允许的命题目标中使用。
<!--ja-->
残る条項は、`order-unfold` から得た二つの枝をそのまま再現しなければなりません。すなわち、誕生がより早い場合と、誕生が等しく、その後に局所的なステップ比較を行う場合です。補助関数はこの場合分けを充足命題の内部に保つので、証人や切り詰められた表の項目は、許される命題の目標の中だけで使われます。
<!--/-->

```agda
           atCmp : ⟨ bornOf α oα a ∈ bornOf α oα c ⟩
                 ⊎ ( (bornOf α oα c ≡ bornOf α oα a)
                   × Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                       (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                       (fst a) (fst c) )
```

<!--en-->
In the earlier-birth branch, the exposed equations for `bornS` rewrite the meta-language membership between the true births as membership between `du` and `dv`. The result is injected into the left side of the object-language disjunction, whose satisfaction is propositionally truncated.
<!--zh-->
在诞生更早分支中，`bornS` 的外显等式把真正诞生层之间的元语言隶属改写为 `du` 与 `dv` 之间的隶属。所得证明进入对象语言析取的左支，而该析取的满足经过命题截断。
<!--ja-->
誕生がより早い枝では、`bornS` について公開された等式により、実際の誕生どうしのメタ言語での所属を `du` と `dv` の所属へ書き換えます。その証明を対象言語の選言の左側へ入れます。この選言の充足は命題的に切り詰められています。
<!--/-->

```agda
                 → ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ ( (var (suc zero) ∈̇ var zero)
                     ∨̇ ( (var zero ≐ var (suc zero))
                       ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ⟩
           atCmp (inl h) = ∣ inl (subst2 (λ p q → ⟨ p ∈ q ⟩)
             (sym (bornS-fst α oα pα a)) (sym (bornS-fst α oα pα c)) h) ∣₁
```

<!--en-->
In the equal-birth branch, the birth equality is rewritten to an equality between `dv` and `du`. The inward adequacy hypothesis `stp-in` then uses the particular recorded value `r`, its table membership, its `IsRel` proof, and the transported `Under` comparison to fill the local step formula. This is precisely the direction in which a concrete local table value is available.
<!--zh-->
在同生分支中，诞生层等式被改写为 `dv` 与 `du` 之间的等式。随后，向内充分性假设 `stp-in` 使用这个特定的记录值 `r`、它在表中的隶属、它的 `IsRel` 证明，以及搬运后的 `Under` 比较，填入局部步进公式。正是在这一方向上，证明手中有一个具体的局部表值。
<!--ja-->
誕生が等しい枝では、誕生の等式を `dv` と `du` の等式へ書き換えます。次に、内向きの妥当性の仮定 `stp-in` が、特定の記録値 `r`、その表への所属、`IsRel` の証明、輸送された `Under` の比較を使って局所ステップ論理式を満たします。具体的な局所表の値が手元にあるのは、まさにこの向きです。
<!--/-->

```agda
           atCmp (inr (e , und)) = ∣ inr
             ( bornS-fst α oα pα c ∙ e ∙ sym (bornS-fst α oα pα a)
             , stp-in (suc zero) (sh4 f) (sh3 zero) (sh2 zero)
                 (dv ∷ du ∷ v ∷ u ∷ γ) odu r hr hrel (moved und) ) ∣₁

```

<!--en-->
Applying this two-branch translation to `cmp` completes the comparison clause of `OrdBody`. Together with the two birth descriptions and the two bounds below `α`, it supplies the deep record required by `CondCore`; it adds no further choice or order-theoretic claim.
<!--zh-->
把这项两分翻译施于 `cmp`，便完成 `OrdBody` 的比较子句。它与两条诞生描述及两条低于 `α` 的界条件共同给出 `CondCore` 所需的深层记录，并未增加新的选择或序论断言。
<!--ja-->
この二つの枝の翻訳を `cmp` に適用すると、`OrdBody` の比較の条項が完成します。二つの誕生の記述と、`α` より下にあるという二つの境界条件と合わせて、`CondCore` が要求する深い記録が得られます。新たな選択や順序論的主張が加わるわけではありません。
<!--/-->

```agda
           side : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ ( (var (suc zero) ∈̇ var zero)
                     ∨̇ ( (var zero ≐ var (suc zero))
                       ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ⟩
           side = atCmp cmp

```

<!--en-->
The pair-level assembly eliminates the truncated existence of the second member: for each candidate `c` related to `a`, the local assembly produces the satisfaction of the core clause.
<!--zh-->
对级组装消去第二个成员的截断存在：对与 `a` 关联的每个候选 `c`，局部组装产出核心子句的满足。
<!--ja-->
対の水準の組み立ては、第二の要素の切り詰められた存在を消去します。`a` と関係づけられるそれぞれの候補 `c` に対して、局所の組み立てが核心の節の充足を産み出します。
<!--/-->

```agda
       atPairs : (o : IsOrd α) → Pairs o → ⟨ γ ⊨ CondCore z tb f ⟩
       atPairs o (a , h) = PT.rec (snd (γ ⊨ CondCore z tb f))
         (λ { (c , (q , hord)) → atRel o a c q hord }) h

```

<!--en-->
The outer payload of `Related` supplies an ordinalness proof `o` and only the propositional truncation of `Pairs o`. Since satisfaction of `CondCore` is a proposition, `atOrd` may eliminate this truncation and pass each represented pair to `atPairs`. Independence from the particular ordinalness proof is used earlier, when `o` is identified with the ambient proof `oα` through `isPropIsOrd`.
<!--zh-->
`Related` 的外层载荷给出一份序数性证明 `o`，以及 `Pairs o` 的命题截断。由于 `CondCore` 的满足是命题，`atOrd` 可以消去这项截断，并把每个表示对交给 `atPairs`。对特定序数性证明的无关性已在更早处使用：借助 `isPropIsOrd`，把 `o` 与环境证明 `oα` 认同。
<!--ja-->
`Related` の外側のペイロードは順序数性の証明 `o` と、`Pairs o` の命題的切り詰めだけを与えます。`CondCore` の充足は命題なので、`atOrd` はこの切り詰めを除去し、表された各対を `atPairs` に渡せます。特定の順序数性の証明に依存しないことは、これより前に `isPropIsOrd` によって `o` と周囲の証明 `oα` を同一視するときに使われています。
<!--/-->

```agda
       atOrd : Σ[ o ∈ IsOrd α ] ∥ Pairs o ∥₁ → ⟨ γ ⊨ CondCore z tb f ⟩
       atOrd (o , h) = PT.rec (snd (γ ⊨ CondCore z tb f)) (atPairs o) h

```

<!--en-->
The specification identifies the satisfaction of the core clause with the relation of the coded pair, as paths of propositions in both directions.
<!--zh-->
该规格把核心子句的满足与编码对的关联等同为命题路径，双向成立。
<!--ja-->
仕様は、核心の節の充足と、符号化された対の関係とを、両方向の命題のパスとして同一視します。
<!--/-->

```agda
     CondCore-spec : (γ ⊨ CondCore z tb f) ≡ Related α (fst (lookup z γ))
     CondCore-spec = ⇔toPath CondCore-out CondCore-in
```

<!--en-->
## The frame's two hypotheses, discharged
<!--zh-->
## 那个框架的两条假设，已解除
<!--ja-->
## フレームの二つの仮定を解消する
<!--/-->

<!--en-->
`Cond` is the form used when the stage and table already occupy variable slots in an ambient environment. The new zeroth slot is reserved for the coded pair being tested, while the old stage and table indices are raised past it. Thus `Cond` introduces no witness for the stage; it refers to the stage already supplied by the surrounding context.
<!--zh-->
当层与表已经占据环境中的变元槽位时，使用 `Cond` 这一形式。新增的第零槽留给待检验的编码有序对，原有的层与表索引则越过它而提升。因此，`Cond` 不为层引入见证，而是引用外围语境已经提供的层。
<!--ja-->
段階と表がすでに周囲の環境の変数スロットにあるときは、`Cond` の形を使います。新しい第零スロットは検査する符号化された順序対のために確保され、もとの段階と表の添字はその先へ持ち上げられます。したがって `Cond` は段階の証人を導入せず、周囲の文脈がすでに与えた段階を参照します。
<!--/-->

```agda
  Cond : ∀ {n} → Fin n → Fin n → Formula S (suc n)
  Cond b f = CondCore zero (var (suc b)) (suc f)

```

<!--en-->
`Cond₀ B F` is the constant-stage form needed by separation. Its sole existential binder supplies a table value and the equality clause pins that value to the fixed constant `F`; the stage is already the constant term `B`. The remaining free slot holds the coded pair under test. The later specification proves that this form and `Cond` describe the same `Related` comparison, still relative to the supplied `StpOut` and `StpIn`; neither form constructs the stage order itself.
<!--zh-->
`Cond₀ B F` 是分离所需的常元层形式。它唯一的存在绑定给出一个表值，等式子句把该值固定为常元 `F`；层本身已经是常元词项 `B`。余下的自由槽保存待检验的编码有序对。后续规格证明这一形式与 `Cond` 描述同一个 `Related` 比较，而这仍相对于给定的 `StpOut` 与 `StpIn`；两种形式都不构造层序本身。
<!--ja-->
`Cond₀ B F` は、分出に必要な定数段階の形です。唯一の存在束縛が表の値を与え、等式の条項がその値を固定した定数 `F` に一致させます。段階はすでに定数項 `B` です。残る自由スロットには、検査される符号化された順序対が入ります。後の仕様は、この形と `Cond` が同じ `Related` の比較を記述することを示しますが、それは依然として与えられた `StpOut` と `StpIn` に相対的です。どちらの形も段階順序そのものを構成しません。
<!--/-->

```agda
  Cond₀ : S → S → Formula S 1
  Cond₀ B F =
    ∃̇ ( (var zero ≐ con F) ∧̇ CondCore (suc zero) (con B) zero )

```

<!--en-->
The variable form tests a possible ordered pair `z` while the stage and the table remain in the ambient environment. Assuming that the stage is ordinal and that the table has the stated value and entry readings, its adequacy equation identifies satisfaction of `Cond` with the host-side class `Related`. Thus this formula describes the already constructed stage comparison; it does not construct a new order.
<!--zh-->
变元形式检验一个可能的有序对 `z`，而层与序表仍留在周围环境中。假设该层是序数，且序表具有给定的取值读式与表项读式，其充分性等式便把 `Cond` 的满足关系与宿主层的类 `Related` 对应起来。因此，这条公式描述的是已经构造好的层序比较，并不构造新的序。
<!--ja-->
変数形式は、段階と順序表を周囲の環境に残したまま、有序対の候補 `z` を調べます。段階が順序数であり、順序表が所定の値と項目の読みをもつと仮定すると、その妥当性の等式は `Cond` の充足をホスト側のクラス `Related` と同一視します。したがって、この論理式はすでに構成された段階順序の比較を記述するのであって、新たな順序を構成するのではありません。
<!--/-->

```agda
  cond-spec : ∀ {n} (b f : Fin n) (γ : S ^ n) → IsOrd (fst (lookup b γ))
            → Values (lookup f γ) (fst (lookup b γ))
            → Entries (lookup f γ) (fst (lookup b γ))
            → (z : S) → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z)
  cond-spec b f γ ob vals ents z =
```

<!--en-->
Prepending `z` moves every old environment slot one place to the right. Consequently the core reads `z` at slot zero, the stage through `var (suc b)`, and the table through `suc f`. With precisely these shifts, the general `CondCore` equation gives the desired variable-form equation directly.
<!--zh-->
把 `z` 加到环境首部后，原有的每个槽位都向后移动一位。因此，核心在零号槽位读取 `z`，经 `var (suc b)` 读取层，并经 `suc f` 读取序表。作出这些平移后，`CondCore` 的一般等式直接给出所需的变元形式等式。
<!--ja-->
`z` を環境の先頭に加えると、もとの各スロットは一つ後ろへ移ります。そこで核心はスロット零で `z` を読み、`var (suc b)` を通して段階を、`suc f` を通して順序表を読みます。このずらしを施せば、`CondCore` の一般的な等式から、必要な変数形式の等式が直接得られます。
<!--/-->

```agda
    CondCore-spec zero (var (suc b)) (suc f) (z ∷ γ) ob vals ents

```

<!--en-->
For separation, the ambient environment contains only the candidate `z`, so the constant form must bind the table it consults. A bound element `c` is suitable when its underlying set equals that of the fixed table `F` and the core comparison holds with `c` in the table slot. The auxiliary proposition `Held c` packages exactly these two facts; `c` is a table representative, not a formula code.
<!--zh-->
作分离时，周围环境只含候选者 `z`，所以常元形式必须绑定它所查阅的序表。若一个被绑定的元素 `c` 的底层集合等于固定序表 `F` 的底层集合，并且以 `c` 占据序表槽位时核心比较成立，那么 `c` 就是合适的见证。辅助命题 `Held c` 恰好合并这两项事实；`c` 是序表的代表，并非公式码。
<!--ja-->
分出を行うとき、周囲の環境には候補 `z` しかないため、定数形式は参照する順序表を束縛しなければなりません。束縛された要素 `c` の基礎集合が固定された順序表 `F` の基礎集合と等しく、`c` を順序表のスロットに置いた核心の比較が成り立つなら、`c` は適切な証人です。補助命題 `Held c` はこの二つの事実をまとめます。`c` は順序表の代表であり、論理式の符号ではありません。
<!--/-->

```agda
  module _ (B F : S) (oB : IsOrd (fst B))
           (vals : Values F (fst B)) (ents : Entries F (fst B)) (z : S) where
    private
      Held : S → Type (ℓ-suc ℓ)
      Held c = (fst c ≡ fst F)
```

<!--en-->
In the two-slot environment `c ∷ z ∷ []`, slot zero is the bound table representative and slot one is the possible ordered pair. The stage is supplied by the constant term `con B`. This arrangement lets the same core express the constant case; when it is read outward, the table readings for `F` must be transferred to the extensionally equal representative `c`.
<!--zh-->
在两槽环境 `c ∷ z ∷ []` 中，零号槽位是被绑定的序表代表，一号槽位是可能的有序对，而层由常元词项 `con B` 给出。这样的安排使同一个核心也能表达常元情形；向外读取时，必须把 `F` 的序表读式转移给与它外延相等的代表 `c`。
<!--ja-->
二スロットの環境 `c ∷ z ∷ []` では、スロット零が束縛された順序表の代表、スロット一が有序対の候補であり、段階は定数項 `con B` で与えられます。この配置により、同じ核心で定数の場合も表せます。外向きに読むときは、`F` についての順序表の読みを、それと外延的に等しい代表 `c` へ移さなければなりません。
<!--/-->

```agda
             × ⟨ (c ∷ z ∷ []) ⊨ CondCore (suc zero) (con B) zero ⟩

```

<!--en-->
The outward direction starts from a propositionally truncated existential witness for the bound table. Since `Related` is itself a proposition, the truncation may be eliminated into that target. The helper `atHeld` reasons under a temporary representative `c` and its two `Held` facts; no representative escapes this proof, so the argument produces neither a canonical witness nor a choice function.
<!--zh-->
向外方向从被绑定序表的命题截断存在见证出发。由于 `Related` 本身是命题，可以把这层命题截断消去到该目标中。辅助定义 `atHeld` 只在局部使用一个临时代表 `c` 及其两项 `Held` 事实；没有任何代表逸出这段证明，所以该论证既不产生规范见证，也不产生选择函数。
<!--ja-->
外向きの証明は、束縛された順序表について、命題的切り詰めを施した存在証人から始まります。`Related` 自体が命題なので、その切り詰めをこの目標へ除去できます。補助定義 `atHeld` は、一時的な代表 `c` と二つの `Held` の事実のもとだけで推論します。代表はこの証明の外へ出ないため、この議論から標準的な証人や選択関数は得られません。
<!--/-->

```agda
    cond₀-out : ⟨ (z ∷ []) ⊨ Cond₀ B F ⟩ → ⟨ Related (fst B) (fst z) ⟩
    cond₀-out = PT.rec (snd (Related (fst B) (fst z))) atHeld
      where
      atHeld : Σ[ c ∈ S ] Held c → ⟨ Related (fst B) (fst z) ⟩
      atHeld (c , (qc , hc)) =
```

<!--en-->
The equality `qc` lets the two table readings cross between the bound representative and `F`, but in opposite directions. An entry assumed in `c` is transported to `F` before `vals` identifies its value as a realization of the stage relation. Conversely, `ents` supplies a propositionally truncated entry in `F`, and mapping under that truncation transports the entry back to `c`.
<!--zh-->
等式 `qc` 使两条序表读式可以在被绑定的代表与 `F` 之间转换，但方向相反。先把假设属于 `c` 的表项运输到 `F`，再由 `vals` 判定其取值实现该层关系。反过来，`ents` 给出 `F` 中一个经过命题截断的表项，而在这层截断之下作映射，把该表项运回 `c`。
<!--ja-->
等式 `qc` によって、二つの順序表の読みを、束縛された代表と `F` の間で互いに逆向きに移せます。`c` にあると仮定した項目は、まず `F` へ運ばれ、その値が段階の関係を実現することを `vals` が示します。逆に、`ents` は `F` にある項目を命題的切り詰めのもとで与え、その内側で写像することにより、項目を `c` へ戻します。
<!--/-->

```agda
        CondCore-out (suc zero) (con B) zero (c ∷ z ∷ []) oB
          (λ x r hx hp → vals x r hx
            (subst (λ w → ⟨ pr (fst x) (fst r) ∈ w ⟩) qc hp))
          (λ x hx → PT.map (λ { (r , hr) → r
              , subst (λ w → ⟨ pr (fst x) (fst r) ∈ w ⟩) (sym qc) hr })
```

<!--en-->
These transported readings are exactly the hypotheses required to read the core comparison outward. Applying them to `hc` yields the `Related` fact for `z`. The entry witness remains propositionally truncated throughout this passage, which is sufficient because both the core satisfaction and the resulting relation claim are propositions.
<!--zh-->
这些经过运输的读式正是向外读取核心比较所需的假设。把它们用于 `hc`，便得到关于 `z` 的 `Related` 事实。在整个转换中，表项见证始终处于命题截断之下；这已经足够，因为核心满足关系与所得关系断言都是命题。
<!--ja-->
こうして移された読みは、核心の比較を外向きに読むために必要な仮定そのものです。それらを `hc` に適用すると、`z` についての `Related` の事実が得られます。この過程を通じて項目の証人は命題的に切り詰められたままですが、核心の充足も得られる関係の主張も命題なので、それで十分です。
<!--/-->

```agda
            (ents x hx))
          hc

```

<!--en-->
For the inward direction there is already a specified table `F`, so it can serve as the existential witness and its equality with the constant table is reflexive. The core inward reading then turns the given `Related` fact into satisfaction with `F` in the table slot. This constructs a witness inside propositional truncation; it does not extract one from truncated information or assert that table representatives are uniquely chosen.
<!--zh-->
向内方向已经给定序表 `F`，所以可直接用它作存在见证，而它与常元序表的等式就是自反性。核心的向内读式随后把给定的 `Related` 事实化为以 `F` 占据序表槽位时的满足证明。这里是在命题截断内部构造见证，并非从截断信息中提取见证，也没有断言序表代表是唯一选定的。
<!--ja-->
内向きには、指定された順序表 `F` がすでにあるので、それ自身を存在証人にでき、定数で指定された順序表との等式は反射性で与えられます。続いて核心の内向きの読みが、与えられた `Related` の事実を、`F` を順序表のスロットに置いた充足へ変えます。ここでは命題的切り詰めの内側に証人を構成しているのであり、切り詰められた情報から証人を取り出したり、順序表の代表が一意に選ばれると主張したりしてはいません。
<!--/-->

```agda
    cond₀-in : ⟨ Related (fst B) (fst z) ⟩ → ⟨ (z ∷ []) ⊨ Cond₀ B F ⟩
    cond₀-in h = ∣ F , (refl
      , CondCore-in (suc zero) (con B) zero (F ∷ z ∷ []) oB vals ents h) ∣₁

```

<!--en-->
The two implications give a path between the satisfaction proposition for `Cond₀ B F` and `Related (fst B) (fst z)`. Hence the constant formula has exactly the same mathematical reading as the variable form under the same ordinality, value, and entry hypotheses. This equality concerns proposition-valued meanings; it does not identify the two formulas syntactically or choose a distinguished presentation of the table.
<!--zh-->
这两个蕴含给出 `Cond₀ B F` 的满足命题与 `Related (fst B) (fst z)` 之间的路径。因此，在同样的序数性、取值与表项假设下，常元公式具有与变元形式完全相同的数学读法。该等式涉及命题值含义，并不在语法上等同两条公式，也不为序表选择一个特出的呈现。
<!--ja-->
二つの含意から、`Cond₀ B F` の充足命題と `Related (fst B) (fst z)` の間の道が得られます。したがって、同じ順序数性、値、項目についての仮定のもとで、定数形式は変数形式とまったく同じ数学的な読みをもちます。この等式は命題値の意味に関するものであり、二つの論理式を構文的に同一視したり、順序表の特別な提示を選んだりするものではありません。
<!--/-->

```agda
  cond₀-spec : (B F : S) → IsOrd (fst B)
             → Values F (fst B) → Entries F (fst B)
             → (z : S) → ((z ∷ []) ⊨ Cond₀ B F) ≡ Related (fst B) (fst z)
  cond₀-spec B F oB vals ents z =
    ⇔toPath (cond₀-out B F oB vals ents z) (cond₀-in B F oB vals ents z)
```

<!--en-->
The generic table construction can now use `Cond` when the stage and table occupy variable slots and `Cond₀` when they are fixed constants. Its resulting relation objects represent the comparison underlying the previously constructed strict well-order `orderAt`; no well-order is rebuilt here. Every result remains relative to `StpOut` and `StpIn` for the abstract step formula. `InternalWellOrder` later supplies those two readings for the concrete step and thereby removes this remaining parameter.
<!--zh-->
通用序表构造现在可以在层与序表占据变元槽位时使用 `Cond`，并在二者作为固定常元时使用 `Cond₀`。由此得到的关系对象表示先前已构造的严格良序 `orderAt` 的底层比较；这里没有重新构造良序。所有结果仍然相对于抽象步进公式的 `StpOut` 与 `StpIn`。随后，`InternalWellOrder` 为具体步进提供这两条读式，从而消去最后这个参数。
<!--ja-->
これで一般的な順序表の構成は、段階と順序表が変数スロットを占める場合には `Cond` を、固定された定数である場合には `Cond₀` を使えます。そこから得られる関係の対象は、先に構成済みの狭義整列順序 `orderAt` の基礎となる比較を表現します。ここで整列順序を作り直してはいません。すべての結果は、抽象的なステップ論理式に対する `StpOut` と `StpIn` に相対的です。後に `InternalWellOrder` が具体的なステップについてこの二つの読みを与え、残るパラメータを除きます。
<!--/-->

```agda

  open Described Cond Cond₀ cond-spec cond₀-spec public
```

<!--en-->
## Recap

The chapter has described, in the object language, the relation underlying the previously constructed stage order. `BirthAt` identifies a birth ordinal only under an external ordinality hypothesis, `CodesAt` determines the moving code set only extensionally, and `CondCore` matches the birth-first comparison only relative to `StpOut`, `StpIn`, `Values`, and `Entries`. All existential, decoding, table-value, and `Under` witnesses remain within propositional truncation. The next chapter supplies the concrete step formula and its two readings.
<!--zh-->
## 小结

本章在对象语言中描述了先前所构造层序的底层关系。`BirthAt` 只有在外部给出序数性假设时才认定诞生序数，`CodesAt` 只在外延意义上确定随载体变化的码集，而 `CondCore` 只有相对于 `StpOut`、`StpIn`、`Values` 与 `Entries` 才与诞生层优先的比较相符。存在、解码、表值与 `Under` 的见证始终留在命题截断之内。下一章将给出具体步进公式及其两条读式。
<!--ja-->
## まとめ

この章では、先に構成された段階順序の基礎となる関係を対象言語で記述しました。`BirthAt` が誕生順序数を同定するのは外から順序数性を仮定した場合だけであり、`CodesAt` が台とともに動く符号集合を定めるのは外延的な意味においてだけです。また、`CondCore` が誕生段階優先の比較と一致するのは、`StpOut`、`StpIn`、`Values`、`Entries` に相対してだけです。存在、復号、表の値、`Under` の証人は、すべて命題的切り詰めの内側にとどまります。次の章で、具体的なステップ論理式とその二つの読みを与えます。
<!--/-->
