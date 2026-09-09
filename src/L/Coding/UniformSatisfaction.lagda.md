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
内部满足关系的使用者直接面对的是一个**码**，而非该码所出自的公式。内部可定义幂集会遍历某阶段处全部元数一的码，良序也可能比较不属于任何共同公式的两个子码。因此递归需要一张定义域为整个阶段码集的表；`AllCodes`{.Agda} 恰好对每个元数都给出这些键。

图以存在方式把表与合格的索引集绑定起来。为了证明某个成员有图值，`funct`{.Agda} 可以取该成员自己的子公式槽；前面的编码章节已经证明那张槽表封闭、全且满足诸子句。统一性随后说明这些局部见证与从整个码集读出的取值相容。

除此之外还需另一个衔接：码集使用**层级**在阶段字母表上的编码，而递归表使用**模型**在模型语言上的编码。本章认同这两种呈现，并导出供幂集与 Choice 使用的统一满足关系表。
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
## 命名编码集的成员
<!--ja-->
## コード集合の要素を名づける
<!--/-->

<!--en-->
The specification of `AllCodes A` turns any member into a formula over members of `A` whose key is that member. The construction `keyIn` packages the resulting key as an element of `L` for use by the recursion.
<!--zh-->
`AllCodes A` 的规格把任意成员化为一个常元取自 `A` 的成员且以该成员为键的公式。构造 `keyIn` 再把所得键封装为 `L` 的元素，供递归使用。
<!--ja-->
`AllCodes A` の仕様は任意の要素から、`A` の要素を定数とし、その要素を鍵にもつ論理式を得ます。`keyIn` は得られた鍵を再帰で使える `L` の要素として包装します。
<!--/-->

<!--en-->
Three lines, and they are the only one-time decision in this chapter. A consumer that
wants the value at a particular formula has to name the member the value is taken
at, and the obvious name is the key itself; naming it that way does not
elaborate, because the key unfolds into a pair of a numeral with a code and that
construction then sits inside the recursion's domain and inside a satisfaction.

So the name is made opaque where it is made. As an opaque definition, it is an
element of `L` that a type can mention without unfolding, and the two facts a
consumer needs come out with it: it lies in the domain, and it is the key of
the formula it was made from. Everything below is stated at a variable member and
reaches its key by an equation, so this opaque name is the only thing that
would need unfolding, and no step unfolds it.
<!--zh-->
这三行是本章仅有的一次性决定。想要某条特定公式处取值的使用者，必须指明「取值所在的那个成员」，而显而易见的名字就是那个键本身；可是这样一来名字无法展开，因为键会展开成「数码与码之对」，而这个构造随后就进入了递归的定义域，也进入了一个满足关系。

因此，这个名字在构造处被封装为不透明定义。封装后，它是 `L` 的一个元素，类型可以提到它而不必展开；同时得到使用者需要的两项事实：它属于定义域，并且是构造它时所用公式的键。后续结论都先对变元成员陈述，再通过等式应用到这个键，因此不会展开这个不透明的名字。
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
`keyBridge` 证明：把一个常元取自 `A` 成员的公式直接编码，与先把常元翻译进 `L` 再取模型内部的公式键，两者所得的底层键相同。随后的框架固定图公式所需的数码标签、塔与编码域。
<!--ja-->
`keyBridge` は、`A` の要素を定数とする論理式を直接符号化した鍵と、定数を `L` へ移してからモデル内部で作った鍵の台が一致することを示します。続く枠組みはグラフ論理式に必要な数項タグ、塔、コード領域を固定します。
<!--/-->

<!--en-->
A key in the hierarchy's coding is the arity numeral paired with the code of the
formula relabelled along the alphabet's embedding; a key in the model's coding is
the numeral of `L` paired with the code taken in `L`. `codeBridge`{.Agda} equates
the two codes, one clause per constructor. It was written in the model chapter
and has not been used since, because this is the statement it was written for.

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
层级编码里的一个键，是元数数码与「沿字母表的嵌入重标之后那条公式的码」之对；模型编码里的一个键，是 `L` 的数码与「在 `L` 里取的码」之对。`codeBridge`{.Agda} 把这两个码等同起来，一个构造子对应一条子句。它写在模型那一章，此后一直没有被使用，因为它当初就是为这条陈述而写的。

它供不出的是那次重标。集合那边的公式在字母表 `⟪ A ⟫`{.Agda} 之上，递归这边的公式在 `L` 之上，故两侧经过的是两个不同的映射，而它们的复合必须被认作一个映射。那是重标的函子性，它归属于重标被定义之处，而如今就在那里；于是整座桥是四次改写，没有归纳。

通往模型的那个映射也不在此处造。它就是桥那一章自己的 `asConst`{.Agda}，即字母表的嵌入接上类包含；而取它而非取一个与它相等的映射，正是使最后一节能够径直引用那条充分性、无须任何翻译步骤的原因。

这座桥只取字母表，别无其他。供诸环境落在其上的那个集合在它里面从未出现，故它比下面那场递归少一个参数；而后面某一章若需要两套编码在「握在一位上的载体」处相符，便可以直接用它，无须供上一个它并不拥有的第二载体。
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
对 `AllCodes B` 的成员所命名的公式，其显式满足关系表在相应键处给出一个输出。满足关系表的键确定性定理证明该处任意两个输出相等，从而给出递归所需的存在性与唯一性。
<!--ja-->
`AllCodes B` の要素が名づける論理式について、明示的な充足関係表は対応する鍵での出力を与えます。表の鍵による決定性定理はその鍵での任意の二出力が等しいことを示し、再帰に必要な存在と一意性を与えます。
<!--/-->

<!--en-->
Both halves come from the previous chapters, applied at the formula the member
is the key of rather than at an ambient formula, and the change makes existence
*shorter*. The per-formula instance had to transport a subformula's entry along the
inclusion of its own subtree into the ambient table; here the recovered formula
**is** the formula whose table is being handed over, so `entry-in`{.Agda} applies
directly and the transport is gone.

The change does not affect uniqueness at all, and the reason is structural.
`Pinned`{.Agda} speaks about the index set and the table the graph produced,
which are bound variables of the caller's environment, never about the
recursion's domain. The domain occurs nowhere in it, nor in the ten clauses,
so changing what the recursion is indexed by cannot reach uniqueness.

Only the totality hypothesis is written out here, and its environment is written
out with it. Left to inference, the graph's three existentially bound slots
determine nothing and six metavariables survive; naming the environment costs one
line and is the difference between elaborating and not.
<!--zh-->
这两半都来自前几章，只是施于「该成员是其键的那条公式」而非某条周遭公式，而这一更换使存在性**更短**。按公式索引的那个实例，得把一条子公式的条目沿「它自己的子树到周遭表的包含」搬过去；此处还原出的那条公式**就是**正在取其表的那条公式，故 `entry-in`{.Agda} 直接适用，那一步搬运就消失了。

这次更换完全不影响唯一性，理由是结构性的。`Pinned`{.Agda} 谈的是「图所产出的索引集与表」，那是调用方环境里的被绑定变元，从不涉及递归的定义域。定义域既不出现在它里面，也不出现在十条子句里，因此更换递归的索引触及不到唯一性。

此处把全性那条假设连同它的环境一并显式写出。若交由推断，图上三个存在绑定的槽位确定不了任何内容，会剩下六个元变元；而点名环境只需一行，那正是「能否被展开求解」的分水岭。
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
`satRec` 以 `AllCodes B`、满足关系图、对子公式的封闭性以及上一节的存在唯一性证明来实例化抽象递归定理；其取值函数就是下文使用的一致满足关系赋值。
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
定义域是该阶段处的码集，图是两章之前的那一个，而 `funct`{.Agda} 经 `mereFunct`{.Agda} 给出，因为「仅仅存在的唯一解」就是可缩解。一个成员以「字母表之上某条公式的键」这种仅仅存在的形式出现，该等式转换把它的等式变成一条关于模型之键的等式，上面两半便施于那个键。

两个载体是彼此独立的参数，且始终如此。`A` 是诸码的常元所取自的字母表；`B` 是诸环境所属的集合；递归中没有任何东西把它们联系起来，而要求递归带上一个用不上的关系，只会得到一条更弱的定理。两者在下一节、且只在下一节才被结合起来，因为只有在那里满足关系才获得含义。
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
`val-at` 把公式键处的递归取值等同于已经证明满足诸子句的显式 `Sat` 值。随后，`val-sat` 把「属于该值」读成：所表示的公式在其编码环境下得到满足。
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
与任何东西都不相连的递归定义不了任何东西，故这个取值要陈述两遍。

先对照递归自身的构造来读，这里用到的正是唯一性：在「是某条公式之键」的那个成员处，取值就是元语言递归在那条公式处造出的那个集合，因为存在性那一半给出以该集合为一个解，而递归的取值是唯一的解。后续使用这张表的证明要从其中取出任何内容，所需的正是这条读式，因为那个值函数来自一次可缩性，自身化简不出任何东西。

那个成员是**变元**，其键通过一条等式给出；这是测量所得的选择，而非表述偏好。若直接在该键上陈述，值函数的实参就是具体的码构造，该构造也会进入「定义该值的图的满足关系」中。同一陈述以变元书写时耗时四秒，直接写在键上则运行超过六分钟后被放弃；把它改写成变元版本的推论时结果相同。这说明代价来自**陈述**而非证明。唯一性一章在第一个情形中记录的规则，在此原样适用。

两个方向都没有丢失内容。已经持有一个成员的使用者，同时持有该成员及其键等式；需要**点名**该成员时，则可通过前面封装的不透明名字取得方便的形式，而且无需展开，因为类型中提到该名字不会触发其定义。
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
再对照满足关系，这是本目标存在的理由。桥那一章证过：元语言那个取值的成员，就是在世界 `(B, ∈)` 中满足该公式的一个环境；把它与上面那条读式复合，同一句话便适用于这场递归所产出的表。在元数一处它特化为可定义幂集所指的那个可定义子集，故**在「是某条公式之键」的那个成员处读出的那张表，就是该公式的可定义子集**，而那正是内部层级将据以读出 `Def`{.Agda} 的陈述。

两个载体在此处合一，而且必须如此：常元皆为载体成员的公式，内层世界可以解读；点名了 `L` 的任意元素的公式则不然，而桥那一章对此已有说明。故下面两条定理陈述在同一个载体上，而这本来也是使用者所需要的实例化：某阶段处的诸码，在同一个阶段之上被满足。
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
`satRec`{.Agda} 作为已内化递归的满足关系，定义在**某阶段处的诸码**之上，而非定义在一条公式的诸子公式之上，而 `Table`{.Agda} 是它产出的那张表。`val-at`{.Agda} 在一个以键的形式给出的成员处读出取值；`val-sat`{.Agda} 说那个取值**就是**载体之上的满足关系。

这里没有任何内容被重新索引或削弱。预先记录的风险是：定义域或其良构谓词可能在无法使用槽位的位置要求把载体作为**常元**；那样就必须在「载体与键」的对上重新索引槽、表、全性与隶属，并在两个方向的十个情形中逐一改写。该风险没有发生：`slot`{.Agda}、`satTable`{.Agda}、`total`{.Agda}、`inSlot`{.Agda}、`slotClosed`{.Agda}、`soundness`{.Agda} 与 `Good.pinned`{.Agda} 在上文都按原有类型直接使用。码载体不会进入那个图；它在码集自身的谓词中被绑定并固定，所得是 `L` 的一个元素，而这正是递归的定义域。

这一切之所以便宜，靠的是图中的那个存在量词；这应当视为一项设计事实，而非侥幸留存的结果。一个以存在量词存放自己的表的图，允许取值由**任意**一张合格的表来担保，因此实例在每个索引处都能用可给出该取值的最小的表作答。倘若图中写明了具体的表，定义域与表就得一起扩大，而前面每一章都要随之修改。

唯一未曾预料的代价出现在陈述中，而不在证明中；本章的测量说明了这一点。在一个**完全展开的**键处读取取值时，键的构造会进入满足关系，因此证明再长也无法使它顺利展开。同一读式在变元成员上检查需四秒，直接写在键上则运行超过六分钟；把它写成变元版本的推论时也有同样差别。解决办法正是两条既有规则：每条读式都以成员为变元，再通过等式转到它的键；调用方需要点名的名字则在构造处封装为不透明定义。前一规则来自唯一性一章，在这里虽无归纳证明仍然适用；后一规则针对出现在目标中的构造，在这里只有一条等式的目标上同样适用。
<!--/-->
