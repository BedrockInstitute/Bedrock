<!--en-->
# Uniform satisfaction over all codes
<!--zh-->
# 全部编码上的一致满足关系
<!--ja-->
# 全コード上の一様な充足関係
<!--/-->

<!--en-->
Recursion on `AllCodes A` produces one satisfaction assignment whose value at every formula key agrees with the explicit satisfaction table for that formula. This makes satisfaction available uniformly across formulas and arities.
<!--zh-->
在 `AllCodes A` 上递归产生一个统一的满足关系赋值，它在每个公式键处的值都与该公式的显式满足关系表相符。于是满足关系可以跨公式与元数一致地使用。
<!--ja-->
`AllCodes A` 上の再帰により一つの充足関係の割当てを作り、各論理式の鍵での値がその論理式の明示的な充足関係表と一致することを示します。これにより論理式とアリティを越えて充足関係を一様に使えます。
<!--/-->

<!--en-->
Consumers of internal satisfaction arrive holding a **code**, not the formula
from which it came. The internal definable powerset ranges over all arity-one
codes at a stage, while the well-order may compare codes that are not subcodes
of any common formula. The recursion therefore needs one table whose visible
domain is the whole stage code set. `AllCodes`{.Agda} supplies exactly those
keys, at every arity.

The graph itself binds a table and a qualifying index set existentially. To show
that a member has a graph value, `funct`{.Agda} may use the member's own
subformula slot, whose closed, total, clause-satisfying table was certified by
the preceding coding chapters. Uniformity then says that these local witnesses
cohere into the value read from the whole code set.

A second bridge is needed because the code set uses the **hierarchy's** coding
over a stage alphabet, whereas the recursive table uses the **model's** coding
over the model language. This chapter identifies the two presentations and
exports the uniform satisfaction table consumed by powerset and Choice.
<!--zh-->
内部满足关系的消费方到场时手里握着的是一个**码**，而不是该码所出自的公式。内部可定义幂集遍历某阶段处全部元数一的码，良序也可能比较不属于任何共同公式的两个子码。因此递归需要一张可见定义域为整个阶段码集的表；`AllCodes`{.Agda} 恰好在每个元数处供应这些键。

图把表与合格索引集作存在绑定。为了证明一个成员有图值，`funct`{.Agda} 可以取该成员自己的子公式槽；前面的编码章节已经证明那张槽表封闭、全且满足诸子句。统一性随后说明这些局部见证与从整个码集读出的取值相容。

还需另一座桥，因为码集使用**层级**在阶段字母表上的编码，而递归表使用**模型**在模型语言上的编码。本章认同这两种呈现，并导出供幂集与 Choice 消费的统一满足关系表。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.UniformSatisfaction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ} using ( domAt; domAt-intro; domAt-out )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
open import L.Coding.SatisfactionBridge {ℓ} lem
  using ( intoL; asConst; Sat-spec ) renaming ( graph to envGraph )
open import L.Coding.SatisfactionTable {ℓ} lem
  using ( keyʟ; slot; satTable; total; inSlot; entry-in )
open import L.Coding.SlotClosure {ℓ} lem using ( slotClosed )
open import L.Coding.EnvironmentTower {ℓ} lem using ( towerAt; module Tower; module TowerHolds )
open import L.Coding.Quantification {ℓ} using ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9 )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.PinnedRecursion {ℓ} lem using ( module SatSoundC; module SlotHolds ) renaming ( keyBridge to keyBridge' )
open import L.Coding.SatisfactionGraph {ℓ} lem using
  ( satGraph; graph-in; graph-out; Bi; Ti; Ci; Ei; NN; ev; numν; numTags )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; AllCodes-out; key∈AllCodes )
open import L.Recursion {ℓ} lem using ( Recursion; mereFunct; module Of )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Naming a member of the code set
<!--zh-->
## 点名编码集的成员
<!--ja-->
## コード集合の要素を名づける
<!--/-->

<!--en-->
The specification of `AllCodes A` turns any member into a formula over members of `A` whose key is that member. The construction `keyIn` packages the resulting key as an element of `L` for use by the recursion.
<!--zh-->
`AllCodes A` 的规格把任意成员化为一个常元取自 `A` 的成员、且以该成员为键的公式。构造 `keyIn` 再把所得键封装为 `L` 的元素，供递归使用。
<!--ja-->
`AllCodes A` の仕様は任意の要素から、`A` の要素を定数とし、その要素を鍵にもつ論理式を得ます。`keyIn` は得られた鍵を再帰で使える `L` の要素として包装します。
<!--/-->

<!--en-->
Three lines, and they are the chapter's one performance decision. A consumer that
wants the value at a particular formula has to name the member the value is taken
at, and the obvious name is the key itself; naming it that way does not
elaborate, because the key unfolds into a pair of a numeral with a code and that
construction then sits inside the recursion's domain and inside a satisfaction.

So the name is sealed where it is made. Sealed, it is an element of `L` that a
type can mention without unfolding, and the two facts a consumer needs come out
with it: it lies in the domain, and it is the key of the formula it was made
from. Everything below is stated at a variable member and reaches its key by an
equation, so the seal is the only thing that has to be opened, and nothing opens
it.
<!--zh-->
三行，而它们是本章唯一的一次性能决定。想要某条特定公式处的取值的消费方，必须为「取值所在的那个成员」点名，而显而易见的名字就是那个键本身；可是那样点名展开不了，因为键会展成「数码与码之对」，而那个构造随后就坐进了递归的定义域里、也坐进了一个满足关系里面。

于是那个名字在它被造出之处封印。封印之后，它是 `L` 的一个元素，类型可以提它而不必展开，而消费方所需的两条事实随之出来：它落在定义域中，且它是「造它时所用的那条公式」的键。下面的一切都陈述在变元成员上、并经一条等式抵达它的键，故需要被打开的只有这个封印，而没有任何东西打开它。
<!--/-->

```agda
module _ (A : S) where
  opaque
    keyIn : ∀ {n} → Formula ⟪ fst A ⟫ n → S
    keyIn ψ = keyS A ψ

    keyIn≡ : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) → fst (keyIn ψ) ≡ fst (keyS A ψ)
    keyIn≡ ψ = refl

    keyIn∈ : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) → ⟨ keyIn ψ ∈ˢ AllCodes A ⟩
    keyIn∈ ψ = key∈AllCodes A ψ
```

<!--en-->
## Relating external and internal formula keys
<!--zh-->
## 关联外部与内部公式键
<!--ja-->
## 外側と内側の論理式の鍵を結ぶ
<!--/-->

<!--en-->
`keyBridge` proves that coding a formula over members of `A` directly gives the same underlying key as first translating its constants into `L` and then using the model-internal key. The accompanying frame fixes the numeral tags, tower, and code domain needed by the graph formula.
<!--zh-->
`keyBridge` 证明：直接编码一个常元取自 `A` 成员的公式，与先把常元翻译进 `L`、再取模型内部公式键，所得底层键相同。随后的框架固定图公式所需的数码标签、塔与编码域。
<!--ja-->
`keyBridge` は、`A` の要素を定数とする論理式を直接符号化した鍵と、定数を `L` へ移してからモデル内部で作った鍵の台が一致することを示します。続く枠組みはグラフ論理式に必要な数項タグ、塔、コード領域を固定します。
<!--/-->

<!--en-->
A key in the hierarchy's coding is the arity numeral paired with the code of the
formula relabelled along the alphabet's embedding; a key in the model's coding is
the numeral of `L` paired with the code taken in `L`. `codeBridge`{.Agda} equates
the two codes, one clause per constructor. It was written in the model chapter
and has had no consumer since, because this is the statement it was written for.

What it does not supply is the relabelling. The set's formulas are over the
alphabet `⟪ A ⟫`{.Agda} and the recursion's formulas are over `L`, so the two
sides pass through two different maps and their composite has to be recognized as
one map. That is functoriality of relabelling, which belongs where relabelling is
defined and is now there, so the whole bridge is four rewrites and no induction.

The map into the model is not built here either. It is the bridge chapter's own
`asConst`{.Agda}, the alphabet's embedding followed by the class inclusion, and
taking that one rather than an equal one is what lets the last section quote the
adequacy without a translation step.

The bridge takes the alphabet and nothing else. The set the environments range
over never appears in it, so it is stated one parameter short of the recursion
below, and a later chapter that needs the two codings to agree at a carrier held
in a slot can use it without supplying a second carrier it does not have.
<!--zh-->
层级编码里的一个键，是元数数码与「沿字母表的嵌入重标之后那条公式的码」之对；模型编码里的一个键，是 `L` 的数码与「在 `L` 里取的码」之对。`codeBridge`{.Agda} 把这两个码等同起来，一构造子一子句。它写在模型那一章，此后一直没有消费方，因为它当初就是为这条陈述而写的。

它供不出的是那次重标。集合那边的公式在字母表 `⟪ A ⟫`{.Agda} 之上，递归这边的公式在 `L` 之上，故两侧经过的是两个不同的映射，而它们的复合必须被认出为一个映射。那是重标的函子性，它归属于重标被定义之处，而如今就在那里；于是整座桥是四次改写，没有归纳。

通往模型的那个映射也不在此处造。它就是桥那一章自己的 `asConst`{.Agda}，即字母表的嵌入接上类包含；而取它、而非取一个与它相等的映射，正是使最后一节能够径直引用那条充分性、无须任何翻译步骤的原因。

这座桥只取字母表，别无其他。诸环境所落之上的那个集合在它里面从未出现，故它比下面那场递归少一个参数；而后面某一章若需要两套编码在「握在一位上的载体」处相符，便可以直接用它，无须供上一个它并不拥有的第二载体。
<!--/-->

```agda
module _ (A : S) where
  keyBridge : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            → fst (keyS A ψ) ≡ fst (keyʟ (mapFo (asConst A) ψ))
  keyBridge = keyBridge' A

module _ (B : S) where
  fr : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → S ^ (14 + n)
  fr φ γ = ev numν (Tower.tower B) (slot B φ) (satTable B φ) B γ

  frTags : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → Tags (fr φ γ) NN
  frTags φ γ = numTags (Tower.tower B) (slot B φ) (satTable B φ) B γ

  frTow : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → ⟨ fr φ γ ⊨ towerAt Ei Bi (NN f0) ⟩
  frTow φ γ = TowerHolds.holds Ei Bi (NN f0) (fr φ γ) B refl refl refl

  frDom : ∀ {m n} (φ : Formula S m) (γ : S ^ n) → ⟨ fr φ γ ⊨ domAt Ti Ci ⟩
  frDom φ γ = domAt-intro Ti Ci (fr φ γ)
    (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot B φ)))
              (λ { (w , hw) → inSlot B φ (fst z) (fst w) hw }) h)
         , (λ h → total B φ (fst z) h))

module _ (A B : S) where
  private
```

<!--en-->
## Existence and uniqueness at a named formula
<!--zh-->
## 命名公式处的存在性与唯一性
<!--ja-->
## 名づけられた論理式での存在と一意性
<!--/-->

<!--en-->
For the formula named by a member of `AllCodes B`, its explicit satisfaction table supplies an output at the corresponding key. The table’s key-determinacy theorem proves that any two outputs there are equal, giving the two hypotheses required by recursion.
<!--zh-->
对 `AllCodes B` 的成员所命名的公式，其显式满足关系表在相应键处给出一个输出。满足关系表的键确定性定理证明该处任意两个输出相等，从而交付递归所需的存在性与唯一性。
<!--ja-->
`AllCodes B` の要素が名づける論理式について、明示的な充足関係表は対応する鍵での出力を与えます。表の鍵による決定性定理はその鍵での任意の二出力が等しいことを示し、再帰に必要な存在と一意性を与えます。
<!--/-->

<!--en-->
Both are the previous chapters', applied at the formula the member is the key
of rather than at an ambient formula, and the change makes existence *shorter*.
The per-formula instance had to transport a subformula's entry along the
inclusion of its own subtree into the ambient table; here the recovered formula
**is** the formula whose table is being handed over, so `entry-in`{.Agda} applies
directly and the transport is gone.

Uniqueness does not notice the change at all, and the reason is structural.
`Pinned`{.Agda} speaks about the index set and the table the graph produced,
which are bound variables of the caller's environment, never about the
recursion's domain. The domain occurs nowhere in it, nor in the ten clauses,
so changing what the recursion is indexed by cannot reach uniqueness.

Only the totality hypothesis is written out here, and its environment is written
out with it. Left to inference, the graph's three existentially bound slots
determine nothing and six metavariables survive; naming the environment costs one
line and is the difference between elaborating and not.
<!--zh-->
两半都是前几章的，只是施于「该成员是其键的那条公式」而非某条周遭公式，而这次更换使存在性**更短**。按公式索引的那个实例得把一条子公式的条目沿「它自己的子树到周遭表的包含」搬过去；此处被还原出来的那条公式**就是**其表正被递出的那条公式，故 `entry-in`{.Agda} 直接适用，那次搬运消失了。

唯一性压根察觉不到这次更换，而理由是结构性的。`Pinned`{.Agda} 谈的是「图所产出的索引集与表」，那是调用方环境里的被绑定变元，从不谈递归的定义域。定义域既不出现在它里面，也不出现在十条子句里，故更换递归的索引，够不着唯一性。

此处只把全性那条假设写出来，而它的环境也一并写出。若交给推断，图那三个存在绑定的槽位什么也决定不了，会剩下六个元变元；把环境点名只花一行，而那正是「能否被展开求解」的分水岭。
<!--/-->

```agda
    toB : ∀ {n} → Formula ⟪ fst B ⟫ n → Formula S n
    toB = mapFo (asConst B)

    exists : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) → fst x ≡ fst (keyʟ (toB ψ))
           → ⟨ (Sat B (toB ψ) ∷ x ∷ []) ⊨ satGraph B ⟩
    exists {n} ψ x k = graph-in B x (Sat B (toB ψ))
      ∣ numν
      , (Tower.tower B
      , (slot B (toB ψ)
      , (satTable B (toB ψ)
      , (B
      , (refl
      , (frTags B (toB ψ) δ2
      , (frTow B (toB ψ) δ2
      , (slotClosed B (toB ψ) (Tower.tower B ∷ numν f0 ∷ numν f1 ∷ numν f2 ∷ numν f3
            ∷ numν f4 ∷ numν f5 ∷ numν f6 ∷ numν f7 ∷ numν f8 ∷ numν f9 ∷ Sat B (toB ψ) ∷ x ∷ [])
      , (frDom B (toB ψ) δ2
      , (subst (λ w → ⟨ pr w (fst (Sat B (toB ψ))) ∈ fst (satTable B (toB ψ)) ⟩) (sym k)
            (entry-in B (toB ψ))
      , SlotHolds.holds B Ti Bi Ci Ei NN (fr B (toB ψ) δ2) refl
          (frTags B (toB ψ) δ2) (frTow B (toB ψ) δ2) ψ refl refl)))))))))) ∣₁
      where δ2 = Sat B (toB ψ) ∷ x ∷ []

    unique : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) → fst x ≡ fst (keyʟ (toB ψ))
           → (y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → y ≡ Sat B (toB ψ)
    unique {n} ψ x k y hy = Σ≡Prop (λ v → snd (isL v))
      (PT.rec (setIsSet (fst y) (fst (Sat B (toB ψ))))
        (λ { (ν , (E , (C , (T , (b , (eb , (tg , (hE , (hc , (hd , (ha , h12))))))))))) →
          SatSoundC.pinned Ti Bi Ci Ei NN (ev ν E C T b (y ∷ x ∷ [])) B eb tg hE hc h12
            ψ (subst (λ u → ⟨ u ∈ fst C ⟩) (k ∙ sym (keyBridge' B ψ))
                 (domAt-out Ti Ci (ev ν E C T b (y ∷ x ∷ [])) hd x y ha)) y
            (subst (λ u → ⟨ pr u (fst y) ∈ fst T ⟩) (k ∙ sym (keyBridge' B ψ)) ha) })
        (graph-out B x y hy))
```

<!--en-->
## Recursion on the whole code set
<!--zh-->
## 全部编码集上的递归
<!--ja-->
## 全コード集合上の再帰
<!--/-->

<!--en-->
`satRec` instantiates the abstract recursion theorem with `AllCodes B`, the satisfaction graph, closure under subformulas, and the preceding existence-and-uniqueness proof. Its value function is the uniform satisfaction assignment used below.
<!--zh-->
`satRec` 以 `AllCodes B`、满足关系图、对子公式的封闭性以及上一节的存在唯一性证明实例化抽象递归定理。其取值函数就是下文使用的一致满足关系赋值。
<!--ja-->
`satRec` は `AllCodes B`、充足関係グラフ、部分式についての閉包性、前節の存在一意性の証明を用いて抽象的な再帰定理を具体化します。その値関数が以下で使う一様な充足関係の割当てです。
<!--/-->

<!--en-->
The domain is the code set at the stage, the graph is the one two chapters back,
and `funct`{.Agda} is filled through `mereFunct`{.Agda}, because a merely existing
unique solution is a contractible one. A member arrives as a mere key of a
formula over the alphabet, the bridge turns its equation into one about the
model's key, and the two halves above are applied at that key.

The two carriers are independent parameters and stay so. `A` is the alphabet the
codes' constants are drawn from; `B` is the set the environments range over;
nothing in the recursion relates them, and charging the recursion for a relation
it does not use would be stating a weaker theorem. They are pinned together in
the next section, and only there, because that is where satisfaction acquires a
meaning.
<!--zh-->
定义域是该阶段处的码集，图是两章之前的那一个，而 `funct`{.Agda} 经 `mereFunct`{.Agda} 交付，因为「仅仅存在的唯一解」就是可缩解。一个成员以「字母表之上某条公式的键」这种仅仅存在的形式到场，那座桥把它的等式变成一条关于模型之键的等式，而上面两半就施于那个键。

两个载体是彼此独立的参数，且保持如此。`A` 是诸码的常元所取自的字母表；`B` 是诸环境所落之上的集合；递归里没有任何东西把它们联系起来，而为一个用不上的关系向递归收费，等于陈述一条更弱的定理。它们在下一节、且只在那里被钉在一起，因为那才是满足关系获得含义的地方。
<!--/-->

```agda
  satRec : Recursion
  Recursion.dom satRec = AllCodes B
  Recursion.graph satRec = satGraph B
  Recursion.funct satRec x x∈ = mereFunct (satGraph B) x
    (PT.map
      (λ { (n , ψ , q) → Sat B (toB ψ)
         , ( exists ψ x (q ∙ keyBridge' B ψ)
           , unique ψ x (q ∙ keyBridge' B ψ) ) })
      (AllCodes-out B x x∈))

  module Table = Of satRec
```

<!--en-->
## Identifying each recursive value
<!--zh-->
## 逐个识别递归取值
<!--ja-->
## 各再帰値を同定する
<!--/-->

<!--en-->
`val-at` identifies the recursive value at a formula key with the explicit `Sat` value already known to satisfy the clauses. The theorem `val-sat` then reads membership in that value as satisfaction of the represented formula under its encoded environment.
<!--zh-->
`val-at` 把公式键处的递归取值等同于已经证明满足诸子句的显式 `Sat` 值。随后 `val-sat` 把属于该值读成：所表示的公式在其编码环境下得到满足。
<!--ja-->
`val-at` は論理式の鍵での再帰値を、すでに各条件を満たすと分かっている明示的な `Sat` の値と同一視します。続く `val-sat` はその値への所属を、表された論理式が符号化環境の下で満たされることとして読みます。
<!--/-->

<!--en-->
A recursion connected to nothing defines nothing, so the value is stated twice.

Against the recursion's own construction first, and that is uniqueness spent in
the other direction: the value at a member that is the key of a formula is the
set the meta-level recursion built at that formula, because the existence half
exhibits that set as a solution and the recursion's value is the only solution.
This is the reading a consumer needs to get anything out of the table at all,
since the value function comes from a contractibility and computes to nothing on
its own.

The member is a **variable** and its key is reached by an equation, and that is a
measurement, not a taste. Stated at the key itself, the value function's argument
is a concrete code construction, which puts that construction inside the graph
satisfaction the value is defined from; the statement that costs four seconds at
a variable ran past six minutes at the key and was abandoned, and so did the same
statement written as a corollary of the variable one, which shows the cost is in
the *statement* and not in the proof. The uniqueness chapter recorded this law at
its first case and it holds here unchanged.

Nothing is lost, in either direction. A consumer holding a member holds it as a
member, with its key equation beside it; and a consumer that wants to *name* the
member gets the convenient form back through the sealed name, at no cost, because
what the type mentions there does not unfold.
<!--zh-->
一场与任何东西都不相连的递归什么也没定义，故那个取值陈述两遍。

先对着递归自己的构造，而那是唯一性反过来花掉：在「是某条公式之键」的那个成员处，取值就是元语言递归在那条公式处造出的那个集合，因为存在性那一半把那个集合作为一个解拿了出来，而递归的取值是唯一的解。这就是消费方要从这张表里取出任何东西所需的读式，因为那个值函数来自一次可缩性，自身不化简出任何东西。

那个成员是**变元**，而它的键经一条等式抵达；这是一次测量，不是口味。若径直陈述在那个键上，值函数的实参就是一个具体的码构造，也就把那个构造塞进了「值据以定义的那个图的满足关系」里；在变元上花四秒的那条陈述，写在键上跑过了六分钟并被放弃，而把它写成变元版本的推论时同样如此，这说明代价在**陈述**里、不在证明里。唯一性那一章在它的第一个情形上记下了这条规矩，而它在此处原样成立。

两个方向都什么也没有失去。手里握着一个成员的消费方，握着的就是一个成员，外加它的键等式；而想把那个成员**点名**的消费方，可经那个封印过的名字把方便的形式拿回来，且分文不花，因为类型在那里所提的东西不会展开。
<!--/-->

```agda
  val-at : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (x : S) (x∈ : ⟨ x ∈ˢ AllCodes B ⟩)
         → fst x ≡ fst (keyS B ψ)
         → Table.val x x∈ ≡ Sat B (toB ψ)
  val-at ψ x x∈ q =
    Table.val-uniq x x∈ (Sat B (toB ψ)) (exists ψ x (q ∙ keyBridge' B ψ))

```

<!--en-->
And against satisfaction, which is the reason to have the goal. The bridge
chapter proved that a member of the meta-level value is an environment satisfying
the formula in the world `(B, ∈)`; composing it with the reading above says the
same of the table this recursion produces. At arity one it specializes to the
definable subset the definable powerset means, so **the table read at a member
that is the key of a formula is that formula's definable subset**, which is the
statement the internal hierarchy will read `Def`{.Agda} off.

The two carriers meet here because this is where they have to. A formula whose
constants are members of the carrier is one the inner world can read; a formula
naming an arbitrary element of `L` is not, and the bridge chapter says so about
itself. So the two theorems below are stated at the one carrier, which is the
instantiation the consumer wants anyway: the codes at a stage, satisfied over
that same stage.
<!--zh-->
再对着满足关系，而那是这个目标存在的理由。桥那一章证过：元语言那个取值的成员，就是在世界 `(B, ∈)` 中满足该公式的一个环境；把它与上面那条读式复合，同一句话便落到这场递归所产出的表上。在元数一处它特化为可定义幂集所指的那个可定义子集，故**在「是某条公式之键」的那个成员处读出的那张表，就是该公式的可定义子集**，而那正是内部层级将据以读出 `Def`{.Agda} 的陈述。

两个载体在此会合，因为此处是它们非会合不可的地方。常元皆为载体成员的公式，内层世界读得了；点名了 `L` 的任意元素的公式则不然，而桥那一章对自己就是这么说的。故下面两条定理陈述在同一个载体上，而那本来也是消费方想要的实例化：某阶段处的诸码，在同一个阶段之上被满足。
<!--/-->

```agda
module _ (A : S) where
  module DA = DefOf (fst A)
  open DA using ( _⊨ᵐ_ )

  val-sat : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            (x : S) (x∈ : ⟨ x ∈ˢ AllCodes A ⟩) → fst x ≡ fst (keyS A ψ)
          → (δ : DA.SM ^ n) (z : S) → fst z ≡ envGraph A δ
          → (z ∈ˢ Table.val A A x x∈) ≡ (δ ⊨ᵐ ψ)
  val-sat ψ x x∈ q δ z qz =
      cong (z ∈ˢ_)
        (val-at A A ψ x x∈ q ∙ cong (Sat A) (sym (mapFo-comp DA.ι (intoL A) ψ)))
    ∙ Sat-spec A (mapFo DA.ι ψ) δ z qz
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι id ψ δ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The construction yields one graph over all formula codes, while `val-at` and `val-sat` ensure that each of its values is the intended satisfaction set rather than merely a solution of the recursion equations.
<!--zh-->
这一构造得到覆盖全部公式编码的一张图，而 `val-at` 与 `val-sat` 保证其中每个取值都是预期的满足关系集，而不只是递归方程的某个解。
<!--ja-->
この構成により全論理式コード上の一つのグラフが得られ、`val-at` と `val-sat` により、その各値が単なる再帰方程式の解ではなく意図した充足集合であることが保証されます。
<!--/-->

<!--en-->
`satRec`{.Agda} is satisfaction as an internalized recursion over **the codes at
a stage**, not over one formula's subformulas, and `Table`{.Agda} is the table it
yields. `val-at`{.Agda} reads a value out at a member given as a key, and
`val-sat`{.Agda} says that value **is** satisfaction over the carrier.

Nothing below was re-indexed and nothing was weakened. The registered risk for
this goal was that the domain or its well-formedness predicate would need the
carrier as a *constant* somewhere it cannot be a slot, which would have re-indexed
the slot, the table, totality and membership at a pair of a carrier and a key, and
charged the two halves a transport for each of their ten cases. It did not
fire, and the direct evidence is that `slot`{.Agda}, `satTable`{.Agda},
`total`{.Agda}, `inSlot`{.Agda}, `slotClosed`{.Agda}, `soundness`{.Agda} and
`Good.pinned`{.Agda} are all applied above at their existing types. The code
carrier never reaches the graph: it is bound and pinned inside the code set's own
predicate, and what comes out is an element of `L`, which is all a domain is.

What made this cheap is the existential in the graph, and it is worth keeping as
a design fact rather than an accident. A graph that quantifies its table
existentially lets a value be justified by *any* admissible table, so an instance
may answer at each index with the smallest table that reaches it. Had the graph
named its table, the domain and the table would have had to grow together and
every earlier chapter would have moved.

The one cost that was not predicted is in the statements, not in the proofs, and
it is the chapter's measurement. A value read at a key *written out* does not
elaborate, at any length of proof, because the key's construction lands inside a
satisfaction; the reading that costs four seconds at a variable member ran past
six minutes at the key, and so did the same statement written as a corollary of
the variable one. Two things fix it and they are the two recorded laws, one each:
every reading takes the member as a variable and reaches its key by an equation,
and the name a consumer would write instead is sealed where it is built. The
first is the uniqueness chapter's law, met again where nothing is being proved by
induction; the second is the law about a construction appearing in a goal, met at
a goal that is a plain equation.
<!--zh-->
`satRec`{.Agda} 是作为已内化递归的满足关系，跑在**某阶段处的诸码**之上，而非跑在一条公式的诸子公式之上，而 `Table`{.Agda} 是它产出的那张表。`val-at`{.Agda} 在一个以键的形式给出的成员处读出取值；`val-sat`{.Agda} 说那个取值**就是**载体之上的满足关系。

底下没有任何东西被重新索引，也没有任何东西被削弱。本目标登记在案的风险是：定义域或它的良构谓词会在某个不能取作槽位之处、把载体当作**常元**来要；那将把槽、表、全性与隶属重新索引在「载体与键」之对上，并为两半的十个情形各记一笔搬运。它没有引爆，而直接的证据是：`slot`{.Agda}、`satTable`{.Agda}、`total`{.Agda}、`inSlot`{.Agda}、`slotClosed`{.Agda}、`soundness`{.Agda} 与 `Good.pinned`{.Agda} 在上面全都是按它们既有的类型施用的。码载体压根到不了那个图：它在码集自己的谓词里被绑定、被钉住，而出来的是 `L` 的一个元素，而定义域无非就是这个。

使这一切便宜的是图里的那个存在量词，而这值得当作一项设计事实、而非一次偶然留存下来。一个把自己的表存在量化的图，允许一个取值由**任意**一张合格的表来担保，故实例可以在每个索引处用「够得着它的最小的表」作答。倘若那个图把自己的表点了名，定义域与表就得一起长大，而前面每一章都要动。

唯一没被预料到的代价落在诸陈述里、不落在诸证明里，而它就是本章的那次测量。在一个**写开了的**键处读出的取值，无论证明写多长都展开不了，因为那个键的构造落进了一个满足关系里面；在变元成员上花四秒的那条读式，写在键上跑过了六分钟，而把它写成变元版本的推论时同样如此。修好它的有两件事，恰是登记在案的两条规矩、一条一件：每条读式都把成员取作变元、并经一条等式抵达它的键；而消费方本会写下的那个名字，在它被造出之处封印。前者是唯一性那一章的规矩，此番出现在一个压根没有在作归纳证明的地方；后者是「关于出现在目标里的构造」的那条规矩，此番出现在一个只是一条等式的目标上。
<!--/-->
