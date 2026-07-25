# Reflecting an existential into a stage

<!--en-->
The separation chapter carved subsets of a stage using formulas whose quantifiers
were already bounded, and that sufficed because a bounded formula asks only about
what a stage already contains. An unbounded existential does not: it asks whether
*somewhere in L* there is a witness, and L is a proper class. To carve with such
a formula, the class-sized question has to be answered inside a set.

It can be, and the argument is Montague's. Fix a matrix and a parameter. If a
witness exists at all, there is a least stage containing one, and that stage is a
set-sized answer to a class-sized question. Run over all parameters drawn from
one stage, bound the answers, and the result is a single stage that answers for
every parameter in the stage below. Iterate that step through the natural numbers
and take the union: the limit answers for its own parameters, because any
parameter of the limit already lies in some finite layer, whose answers were
bounded at the next.

The choice of witness is where a well-ordering of L is usually invoked, and it is
not needed. What the argument wants is a canonical *ordinal*, not a canonical
element, and the ordinals are already well-ordered by membership. So the least
stage that has a witness is taken directly, by the descent of the stage chapter,
and which witness lives there is never decided. The chapter therefore costs one
use of the excluded middle it already had, and the well-ordering of L stays where
it belongs, with the axiom of choice.
<!--zh-->
分离那一章用量词已然有界的公式雕出阶段的子集，而那是够用的，因为有界公式只问阶段已经装下的东西。无界的存在量词不然：它问的是**在 L 的某处**是否有见证，而 L 是真类。要用这样的公式来雕，就得在一个集合之内回答一个真类大小的问题。

回答得了，而论证出自 Montague。固定一个矩阵与一个参数。若见证根本存在，则有一个包含见证的最小阶段，而那个阶段是对真类大小之问题的集合大小的回答。取遍某一阶段中的全部参数，把诸回答界住，所得便是单一阶段，它为下方那个阶段中的每个参数作答。沿自然数迭代这一步并取并：极限为它自己的参数作答，因为极限的任何参数早已落在某个有穷层里，而那一层的回答在下一层被界住。

见证的选取正是通常召唤 L 的良序之处，而它并不需要。论证想要的是典范的**序数**，而非典范的元素，而序数早已被成员关系良序化。故有见证的最小阶段被直接取用，经阶段那一章的下降，而住在那里的究竟是哪个见证，从未被决定。本章因而只花掉它本已持有的那一次排中律，而 L 的良序留在它该在的地方，与选择公理一处。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Reflect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-in; Lset-out
        ; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd; bound2; setUnion-ord )
open import L.Stage {ℓ} lem using ( LeastOrd; leastOrd )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_; union-ax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
Throughout, the matrix is a formula in two variables, the first the witness and
the second the parameter, and satisfaction is at the class model. An element of a
stage becomes an element of that model by the tower's membership criterion, which
is what lets a stage's index set be used as a supply of parameters.
<!--zh-->
自始至终，矩阵是一条二元公式，第一个变元是见证，第二个是参数，而满足取在类模型处。阶段的一个元素经塔的隶属判据成为该模型的一个元素，正是这一点使阶段的索引集可以充当参数的供给。
<!--/-->

```agda
LsetElt : (β : V ℓ) → IsOrd β → ⟪ Lset β ⟫ → S
LsetElt β oβ m = ⟪ Lset β ⟫↪ m
               , Lset→isL β oβ (⟪ Lset β ⟫↪ m)
                   (∈∈ₛ {a = ⟪ Lset β ⟫↪ m} {b = Lset β} .snd (∈ₛ⟪ Lset β ⟫↪ m))

Sat : (ψ : Formula S 2) (p : S) → S → Ω
Sat ψ p q = (q ∷ p ∷ []) ⊨ ψ

SatEx : (ψ : Formula S 2) (p : S) → Ω
SatEx ψ p = ∃[ q ∶ S ] Sat ψ p q
```

<!--en-->
One transport is needed throughout, and it is worth isolating. Two elements of
the model with the same underlying set are equal, because constructibility is a
proposition; so satisfaction moves along an equality of underlying sets in the
parameter slot. This holds for every matrix, bounded or not: nothing about the
formula is inspected, only the equality of the environments.
<!--zh-->
全章需要一次搬运，值得单独隔出。模型中底集相同的两个元素相等，因为可构造性是命题；故满足关系可沿参数槽中底集的相等而搬运。这对每个矩阵都成立，无论有界与否：公式本身分毫未被检视，被检视的只是环境的相等。
<!--/-->

```agda
⊨param : (ψ : Formula S 2) (q p p' : S) → fst p ≡ fst p'
       → ⟨ Sat ψ p q ⟩ → ⟨ Sat ψ p' q ⟩
⊨param ψ q p p' e =
  subst (λ r → ⟨ Sat ψ r q ⟩) (Σ≡Prop (λ x → (isL x) .snd) e)
```

<!--en-->
## The answering stage
<!--zh-->
## 作答的阶段
<!--/-->

<!--en-->
"Some witness for this parameter lives in this stage" is a property of ordinals,
so the stage chapter's descent applies to it directly. Its premise is that some
ordinal has the property, which follows from satisfiability alone: a witness is
an element of L, and an element of L lies in some stage by definition.

Totality then wants a value even when no witness exists, and the excluded middle
supplies the case distinction. As in the stage chapter, the distinction is made
by an explicit auxiliary rather than by a `with`, because the load-bearing lemma
below has to name the very same decision value and match on it.
<!--zh-->
「这个参数的某个见证住在这个阶段里」是序数的一条性质，故阶段那一章的下降直接适用于它。它的前提是某个序数具有该性质，而这仅凭可满足性即得：见证是 L 的元素，而 L 的元素按定义落在某个阶段里。

其次，全函数性要求即便见证不存在也得有个值，而排中律给出分情形。一如阶段那一章，分情形由显式的辅助函数而非 `with` 作出，因为下面那条承重引理必须点名同一个判定值并在其上匹配。
<!--/-->

```agda
Wit : (ψ : Formula S 2) (p : S) → V ℓ → Ω
Wit ψ p σ = ∃[ q ∶ S ] ((fst q ∈ Lset σ) ⊓ Sat ψ p q)

witnessed : (ψ : Formula S 2) (p : S) → ⟨ SatEx ψ p ⟩
          → ∥ (Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ Wit ψ p α ⟩)) ∥₁
witnessed ψ p = PT.rec squash₁
  (λ { (q , satq) → PT.map
      (λ { (α , (oα , q∈Lα)) → α , (oα , ∣ q , (q∈Lα , satq) ∣₁) })
      (q .snd) })

pick : (ψ : Formula S 2) (p : S) → ⟨ SatEx ψ p ⟩ → LeastOrd (Wit ψ p)
pick ψ p sat = leastOrd (Wit ψ p) (witnessed ψ p sat)

decideStage : (ψ : Formula S 2) (p : S)
            → ⟨ SatEx ψ p ⟩ ⊎ (⟨ SatEx ψ p ⟩ → Empty.⊥) → V ℓ
decideStage ψ p (inl sat) = pick ψ p sat .fst
decideStage ψ p (inr _)   = ∅

pickStage : (ψ : Formula S 2) (p : S) → V ℓ
pickStage ψ p = decideStage ψ p (lem (SatEx ψ p))

decideStage-ord : (ψ : Formula S 2) (p : S)
                  (d : ⟨ SatEx ψ p ⟩ ⊎ (⟨ SatEx ψ p ⟩ → Empty.⊥))
                → IsOrd (decideStage ψ p d)
decideStage-ord ψ p (inl sat) = pick ψ p sat .snd .fst
decideStage-ord ψ p (inr _)   = ∅-ord

pickStage-ord : (ψ : Formula S 2) (p : S) → IsOrd (pickStage ψ p)
pickStage-ord ψ p = decideStage-ord ψ p (lem (SatEx ψ p))
```

<!--en-->
And the property the whole construction rests on: if the parameter is satisfiable
at all, its answering stage really does hold a witness. The proof has to know
which branch the decision took, and it cannot ask, because the decision is a
value of the excluded middle and nothing computes it. So it does the standard
thing: quantify over the branch, remember the equation that the branch *is* the
decision, and transport along it. In the false branch the hypothesis refutes
itself.
<!--zh-->
以及整个构造所倚赖的那条性质：若参数根本可满足，则它的作答阶段确实装着一个见证。证明必须知道判定走的是哪一支，而它问不出来，因为判定是排中律的一个值，没有东西算得出它。于是它做那件标准的事：对分支作量化，记住「该分支**就是**那个判定」这条等式，并沿之搬运。在假分支上，假设自我反驳。
<!--/-->

```agda
pickWitness : (ψ : Formula S 2) (p : S) → ⟨ SatEx ψ p ⟩
            → ⟨ Wit ψ p (pickStage ψ p) ⟩
pickWitness ψ p sat = go (lem (SatEx ψ p)) refl
  where
  go : (d : ⟨ SatEx ψ p ⟩ ⊎ (⟨ SatEx ψ p ⟩ → Empty.⊥))
     → lem (SatEx ψ p) ≡ d → ⟨ Wit ψ p (pickStage ψ p) ⟩
  go (inl s) e = subst (λ d → ⟨ Wit ψ p (decideStage ψ p d) ⟩) (sym e)
                   (pick ψ p s .snd .snd .fst)
  go (inr ¬s) e = Empty.rec (¬s sat)
```

<!--en-->
## One step of closure
<!--zh-->
## 闭包的一步
<!--/-->

<!--en-->
A stage's index set is a type of the ambient size, so the bounding lemma applies
to it: the answering stages of all the parameters drawn from one stage have a
common bound. Merging that bound with the stage itself gives the step function,
which therefore both contains its argument, so that iterating it climbs, and
contains every answer for the argument's parameters.

The step is sealed. Unfolded, it is a bound built from a bound built from the
excluded middle, and the closure argument below matches on stages repeatedly; a
transparent definition would push that whole tower into every conversion check.
The three properties open the seal once each, and the last of them, that an
answering stage lands in the step, is the one place transitivity is used, so the
chain from the answer through the bound into the step is closed inside the seal
and the caller sees only its conclusion.
<!--zh-->
阶段的索引集是周遭大小的类型，故界层引理适用于它：取自同一阶段的全部参数，其作答阶段有公共上界。把那个上界与该阶段本身合并，就得到步进函数，它因而既包含自己的自变量，使迭代得以攀升，又包含自变量的诸参数的每个回答。

步进被封印。展开来，它是由排中律所造之界再造之界，而下面的闭包论证反复在阶段上匹配；透明的定义会把那整座塔推进每一次转换检查。三条性质各开封一次，其中最后一条，即作答阶段落入步进，是唯一用到传递性之处，故从回答经上界进入步进的这条链封在印内，调用方只见其结论。
<!--/-->

```agda
module _ (ψ : Formula S 2) where

  Fbnd : (σ : V ℓ) (oσ : IsOrd σ)
       → Σ[ β ∈ V ℓ ]
           (IsOrd β × ((m : ⟪ Lset σ ⟫) → ⟨ pickStage ψ (LsetElt σ oσ m) ∈ β ⟩))
  Fbnd σ oσ = boundingOrd ⟪ Lset σ ⟫ (λ m → pickStage ψ (LsetElt σ oσ m))
                (λ m → pickStage-ord ψ (LsetElt σ oσ m))

  opaque
    Fstep : (σ : V ℓ) → IsOrd σ → V ℓ
    Fstep σ oσ = bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .fst

  opaque
    unfolding Fstep

    Fstep-ord : (σ : V ℓ) (oσ : IsOrd σ) → IsOrd (Fstep σ oσ)
    Fstep-ord σ oσ = bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .fst

    σ∈Fstep : (σ : V ℓ) (oσ : IsOrd σ) → ⟨ σ ∈ Fstep σ oσ ⟩
    σ∈Fstep σ oσ =
      bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .snd

    pickLand : (σ : V ℓ) (oσ : IsOrd σ) (m : ⟪ Lset σ ⟫)
             → ⟨ pickStage ψ (LsetElt σ oσ m) ∈ Fstep σ oσ ⟩
    pickLand σ oσ m =
      Fstep-ord σ oσ .fst {x = Fbnd σ oσ .fst}
                          {y = pickStage ψ (LsetElt σ oσ m)}
        (Fbnd σ oσ .snd .snd m)
        (bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .fst)
```

<!--en-->
## The limit
<!--zh-->
## 极限
<!--/-->

<!--en-->
Iterate the step from the empty ordinal and union the results. Each layer is an
ordinal because the step preserves being one, and the union of a family of
ordinals is an ordinal, which is the bounding chapter's other export. Each finite
layer belongs to the limit, since it belongs to its own successor and the
successor is one of the sets being unioned.
<!--zh-->
自空序数迭代该步进，并对所得取并。每一层都是序数，因为步进保持序数性，而序数族之并是序数，这是界层那一章的另一件出口。每个有穷层都属于极限，因为它属于自己的后继，而后继是被取并的集合之一。
<!--/-->

```agda
  βₙ : ℕ → V ℓ
  βₙ-ord : (n : ℕ) → IsOrd (βₙ n)
  βₙ zero        = ∅
  βₙ (suc n)     = Fstep (βₙ n) (βₙ-ord n)
  βₙ-ord zero    = ∅-ord
  βₙ-ord (suc n) = Fstep-ord (βₙ n) (βₙ-ord n)

  βₙ-step : (n : ℕ) → ⟨ βₙ n ∈ βₙ (suc n) ⟩
  βₙ-step n = σ∈Fstep (βₙ n) (βₙ-ord n)

  βfam : Lift {ℓ-zero} {ℓ} ℕ → V ℓ
  βfam k = βₙ (lower k)

  βω : V ℓ
  βω = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) βfam)

  βω-ord : IsOrd βω
  βω-ord = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) βfam (λ k → βₙ-ord (lower k))

  βₙ∈βω : (n : ℕ) → ⟨ βₙ n ∈ βω ⟩
  βₙ∈βω n = ∈∈ₛ {a = βₙ n} {b = βω} .snd
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) βfam) (βₙ n) .snd
      ∣ βₙ (suc n)
      , ( ∈∈ₛ {a = βₙ (suc n)} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) βfam} .fst
            ∣ lift (suc n) , refl ∣₁
        , ∈∈ₛ {a = βₙ n} {b = βₙ (suc n)} .fst (βₙ-step n) ) ∣₁)
```

<!--en-->
## Locating a parameter
<!--zh-->
## 为参数定位
<!--/-->

<!--en-->
The closure argument needs its parameter to sit in a finite layer, not merely in
the limit. Two inversions get it there. An ordinal in the limit belongs to one of
the sets being unioned, hence to a finite layer. And a set in the stage of the
limit belongs, by the tower's characterization, to the operator applied to the
stage of some smaller ordinal; locating that ordinal in a finite layer and going
back in places the set in that layer's stage.
<!--zh-->
闭包论证要它的参数落在某个有穷层里，而不只是落在极限里。两次反演把它送到那里。极限中的序数属于被取并的集合之一，因而属于某个有穷层。而极限之阶段中的集合，按塔的刻画，属于某个更小序数之阶段上的算子；把那个序数定位到一个有穷层，再走「进去」，就把该集合放进了那一层的阶段。
<!--/-->

```agda
δ∈βω→fin : (ψ : Formula S 2) (δ : V ℓ) → ⟨ δ ∈ βω ψ ⟩
         → ∥ (Σ[ N ∈ ℕ ] ⟨ δ ∈ βₙ ψ N ⟩) ∥₁
δ∈βω→fin ψ δ δ∈ = PT.rec squash₁
  (λ { (v , (v∈ₛsett , δ∈ₛv)) → PT.map
      (λ { (k , βk≡v) → lower k
         , ∈∈ₛ {a = δ} {b = βₙ ψ (lower k)} .snd
             (subst (λ w → ⟨ δ ∈ₛ w ⟩) (sym βk≡v) δ∈ₛv) })
      (∈∈ₛ {a = v} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) (βfam ψ)} .snd v∈ₛsett) })
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) (βfam ψ)) δ .fst
    (∈∈ₛ {a = δ} {b = βω ψ} .fst δ∈))

localize : (ψ : Formula S 2) (e : V ℓ) → ⟨ e ∈ Lset (βω ψ) ⟩
         → ∥ (Σ[ N ∈ ℕ ] ⟨ e ∈ Lset (βₙ ψ N) ⟩) ∥₁
localize ψ e e∈ = PT.rec squash₁
  (λ { (δ , (δ∈βω , e∈𝒟ₒδ)) → PT.map
      (λ { (N , δ∈βₙN) → N , Lset-in (βₙ ψ N) δ e δ∈βₙN e∈𝒟ₒδ })
      (δ∈βω→fin ψ δ δ∈βω) })
  (Lset-out (βω ψ) e e∈)
```

<!--en-->
## Closure
<!--zh-->
## 闭包
<!--/-->

<!--en-->
The limit answers for its own parameters. Given a parameter whose underlying set
lies in the limit's stage, and a witness somewhere in L, there is a witness in
the limit's stage.

Locate the parameter in a finite layer, and name it there: it is the image of
some index of that layer's stage, so it is one of the parameters the step
function answered for, up to an equality of underlying sets that the transport
absorbs. The answering stage of that parameter belongs to the next layer, so
whatever lives in the answering stage lives in the next layer's stage, and hence
in the limit's; two applications of monotonicity, and the transport back.

The heavy ordinal facts are passed as arguments rather than projected in place.
Their definitions unfold through the bounding lemma into the excluded middle, and
a proof that mentions them by their definitions asks the conversion checker to
walk that unfolding at every step; as arguments they are variables, and stay
variables.
<!--zh-->
极限为它自己的参数作答。给定一个底集落在极限之阶段中的参数，以及 L 中某处的一个见证，则极限之阶段中就有一个见证。

把参数定位到某个有穷层，并在那里为它命名：它是那一层之阶段的某个索引的像，故它是步进函数已经为之作答的诸参数之一，至多相差一个底集的等式，而那个等式由搬运吸收。该参数的作答阶段属于下一层，故住在作答阶段里的东西便住在下一层的阶段里，因而住在极限的阶段里；两次单调性，再搬运回来。

沉重的序数事实作为参数传入，而非就地投影。它们的定义经界层引理一路展开到排中律，而一个按定义提到它们的证明，等于要求转换检查器在每一步都走一遍那次展开；作为参数它们是变元，并且始终是变元。
<!--/-->

```agda
land : (ψ : Formula S 2) (q : S) (σ βsuc : V ℓ)
     → ⟨ fst q ∈ Lset σ ⟩ → ⟨ σ ∈ βsuc ⟩ → ⟨ βsuc ∈ βω ψ ⟩
     → ⟨ fst q ∈ Lset (βω ψ) ⟩
land ψ q σ βsuc fq∈σ σ∈βsuc βsuc∈βω =
  Lset-mono {α = βω ψ} {β = βsuc} βsuc∈βω
    (Lset-mono {α = βsuc} {β = σ} σ∈βsuc fq∈σ)

closure : (ψ : Formula S 2) (p : S) → ⟨ fst p ∈ Lset (βω ψ) ⟩
        → ⟨ SatEx ψ p ⟩ → ⟨ Wit ψ p (βω ψ) ⟩
closure ψ p fp∈βω sat = PT.rec squash₁ atLayer (localize ψ (fst p) fp∈βω)
  where
  atLayer : Σ[ N ∈ ℕ ] ⟨ fst p ∈ Lset (βₙ ψ N) ⟩ → ⟨ Wit ψ p (βω ψ) ⟩
  atLayer (N , fp∈σ) = PT.map found (pickWitness ψ pₘ satₘ)
    where
    σ : V ℓ
    σ = βₙ ψ N
    oσ : IsOrd σ
    oσ = βₙ-ord ψ N
    m : ⟪ Lset σ ⟫
    m = ∈-asFiber {a = fst p} {b = Lset σ} fp∈σ .fst
    pₘ : S
    pₘ = LsetElt σ oσ m
    fpₘ≡fp : fst pₘ ≡ fst p
    fpₘ≡fp = ∈-asFiber {a = fst p} {b = Lset σ} fp∈σ .snd
    satₘ : ⟨ SatEx ψ pₘ ⟩
    satₘ = PT.map (λ { (r , φr) → r , ⊨param ψ r p pₘ (sym fpₘ≡fp) φr }) sat
    pick∈βsuc : ⟨ pickStage ψ pₘ ∈ βₙ ψ (suc N) ⟩
    pick∈βsuc = pickLand ψ σ oσ m
    found : Σ[ q ∈ S ] (⟨ fst q ∈ Lset (pickStage ψ pₘ) ⟩ × ⟨ Sat ψ pₘ q ⟩)
          → Σ[ q ∈ S ] (⟨ fst q ∈ Lset (βω ψ) ⟩ × ⟨ Sat ψ p q ⟩)
    found (q , (fq∈pick , satq)) = q
      , ( land ψ q (pickStage ψ pₘ) (βₙ ψ (suc N))
            fq∈pick pick∈βsuc (βₙ∈βω ψ (suc N))
        , ⊨param ψ q pₘ p fpₘ≡fp satq )
```

<!--en-->
## The reflection theorem
<!--zh-->
## 反射定理
<!--/-->

<!--en-->
Now the statement the separation chapter will consume. For a parameter in the
limit's stage, the class model satisfies the existential exactly when a witness
lies in the limit's stage. Forwards is closure; backwards is forgetting where the
witness lives.

The forward direction needs no translation step, because the two sides are the
same proposition already: the semantics of an existential quantifier is the
truncated sum over the carrier, and that is what `SatEx`{.Agda} was defined to be.
So the theorem is closure with its statement rewritten, and nothing is paid to
cross between syntax and the meta-level.
<!--zh-->
现在是分离那一章将要消费的陈述。对极限之阶段中的参数，类模型满足那个存在量词，恰当极限之阶段中有一个见证。正向是闭包，反向是忘掉见证住在哪里。

正向不需要翻译的一步，因为两侧本已是同一个命题：存在量词的语义是沿载体的截断和，而 `SatEx`{.Agda} 当初就是照这个定义的。故定理是闭包换了个说法，而在语法与元层之间往返，分文未付。
<!--/-->

```agda
reflect-fwd : (ψ : Formula S 2) (p : S) → ⟨ fst p ∈ Lset (βω ψ) ⟩
            → ⟨ (p ∷ []) ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ p (βω ψ) ⟩
reflect-fwd = closure

reflect-bwd : (ψ : Formula S 2) (p : S)
            → ⟨ Wit ψ p (βω ψ) ⟩ → ⟨ (p ∷ []) ⊨ (∃̇ ψ) ⟩
reflect-bwd ψ p = PT.map (λ { (q , (_ , satq)) → q , satq })

reflect : (ψ : Formula S 2) (p : S) → ⟨ fst p ∈ Lset (βω ψ) ⟩
        → ((p ∷ []) ⊨ (∃̇ ψ)) ≡ Wit ψ p (βω ψ)
reflect ψ p fp∈βω = ⇔toPath (reflect-fwd ψ p fp∈βω) (reflect-bwd ψ p)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`βω`{.Agda} is a stage that answers, for every parameter it contains, whether a
matrix has a witness in L, and `reflect`{.Agda} says so: an existential is true
at the class model exactly when it is witnessed inside that stage.

The construction used the excluded middle twice, once to decide satisfiability
and once inside the descent, and used the axiom of choice not at all. That is the
point of taking the least *stage* rather than the least *witness*: the ordinals
come well-ordered, and nothing here has to ask for a well-ordering of L.

What is delivered is the single-parameter, single-quantifier case. Carrying a
tuple of parameters and iterating through a block of quantifiers are the two
extensions the axioms still to be paid will want, and both reuse this chapter's
step function unchanged.
<!--zh-->
`βω`{.Agda} 是这样一个阶段：对它所包含的每个参数，它都回答了某矩阵在 L 中是否有见证，而 `reflect`{.Agda} 正是这么说的：一个存在量词在类模型处为真，恰当它在那个阶段之内被见证。

这个构造用了两次排中律，一次判定可满足性，一次在下降之内，而选择公理一次也没用。这正是取最小**阶段**而非最小**见证**的用意：序数自带良序，而此处没有任何东西需要索取 L 的良序。

交付的是单参数、单量词的情形。携带参数元组与沿一串量词迭代，是尚待偿付的诸公理将会想要的两项推广，而两者都原样复用本章的步进函数。
<!--/-->
