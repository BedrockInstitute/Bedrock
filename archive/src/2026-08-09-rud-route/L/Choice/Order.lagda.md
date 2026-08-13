# The step described, and the table made unconditional

<!--en-->
Every chapter of this part has handed its remainder to the next one, and the
remainder is now a single formula. The frame that turns the order at a stage from
a description into an object (`L.Choice.Table`{.Agda}'s `Described`{.Agda}, applied
through `L.Choice.Faithful`{.Agda}'s `Ordered`{.Agda}) asks for one thing it does
not have: a description of the **step**, saying of two members of a stage's
definable subsets that the naming comparison puts the first before the second.

Everything that description needs is already built. The naming comparison is
described in the object language, and its adequacy against the meta comparison is
proven, on a frame that hands every relation slot the hypothesis of **which order
it holds**. The code slot of that frame is filled unconditionally by the order on
the limit stage. The carrier slot is filled by the table's own readings, and those
readings were restated at "whatever realizes the class", which is exactly what
the step parameter is handed. So the two ends meet, and this chapter is assembly:
no new idea, only the writing down.

The description binds **six** sets and pins **two** constants. The six are the
tower at the stage, its definable subsets, the table's value at the stage, and the
code set over the tower, together with the two pinned ones. The two pinned by an
object equality are the order on the codes and the code set at the empty alphabet,
because a slot takes a variable and those two are particular sets, not descriptions.
The body at those seven slots is the internalized step. Then two readings, by
unpacking and packing the six binders, and then **one line** opens the frame.
<!--zh-->
本部的每一章都把自己的余数交给了下一章，而余数如今只剩一条公式。把阶段处的序由描述变成对象的那个框架 (`L.Choice.Table`{.Agda} 的 `Described`{.Agda}，经 `L.Choice.Faithful`{.Agda} 的 `Ordered`{.Agda} 施用) 索取一样它没有的东西：一条关于**那一步**的描述，它对一个阶段的可定义子集中的两个成员说，命名比较把前者排在后者之前。

那条描述所需的一切都已造好。命名比较已在对象语言里描述出来，它对着元层面比较的充分性也已证出，且所站的框架为每个关系位都带上「它持有的是哪个序」这条假设。那个框架为诸码所设的位由极限阶段上的序无条件填上。载体那一位则由表自己的诸读式填上，而那些读式已被重述在「无论什么实现那个类」之处，那恰恰正是步进参数所被交予的东西。于是两端会合，本章只是装配：没有新想法，只有把它写下来。

那条描述绑定**六**个集合并钉住**两**个常量。六个是阶段处的塔、它的可定义子集、表在该阶段的取值、以及塔之上的码集，连同被钉住的那两个。用对象等词钉住的两个是诸码之上的序与空字母表处的码集，因为一个槽位取的是变元，而那两样是特定的集合、不是描述。落在那七个槽位上的主体就是已内化的那一步。随后是两条读式，靠拆开与装回那六个绑定给出，再随后，**一行**打开那个框架。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Order {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS; 𝒟ₒS; ∅ʟ; Lset-suc )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem
  using ( Mem; New; relOf; carry; orderAt; Under
        ; stepAt-fill; stepAt-read; IsLeastName; leastNameOf )
open import L.Choice.Name {ℓ} lem using ( module Naming )
open import L.Choice.Internal {ℓ} lem using ( StepAt )
open import L.Choice.Table {ℓ} lem using ( IsRel; ixRel-fill; ixRel-rep )
open import L.Choice.Faithful {ℓ} lem
  using ( CodesAt; CodesAt-in; CodesAt-out; stepOrder; module Ordered )
open import L.Choice.Adequate {ℓ} lem using ( module At )
open import L.Choice.Before {ℓ} lem
  using ( codeOrder; codeOrder-fill; codeOrder-rep )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt; DefAt-stage )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )

import FOL.Absoluteness
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))

  iTow iRel iCod iOrd iNil
    : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  iTow = suc (suc (suc (suc (suc zero))))
  iRel = suc (suc (suc zero))
  iCod = suc (suc zero)
  iOrd = suc zero
  iNil = zero
```

<!--en-->
## The elements the description binds

Two of the six sets are computed from the stage: the tower there, and its
definable subsets. Both are elements of the model, that is, pairs of a set and a
proof that it is constructible, and both are **sealed where they are built**, with
one reading each saying what the set half is. This is the law the birth
description measured at 178 s against 2 s, and nothing about that measurement was
local to it: an element that reaches a slot inside a satisfaction is unfolded by
conversion every time the satisfaction is read, and the seal is what stops that.
<!--zh-->
## 描述所绑定的诸元素

六个集合中有两个是从阶段算出来的：那里的塔，以及它的可定义子集。二者都是模型的元素，亦即一个集合与一份「它是可构造的」的证明所成的对，且二者都**在被造出之处封印**，各配一条读式说出它的集合那一半是什么。这正是诞生描述实测为 178 秒对 2 秒的那条定律，而那次实测没有任何一处是它自己所特有的：一个抵达满足关系内部某个槽位的元素，每次那个满足关系被读时都会被转换检查展开，而封印正是止住这件事的东西。
<!--/-->

```agda
-- perf: the elements the step description binds are sealed where they are built,
-- as the birth description's were (measured there at 178 s against 2 s)
opaque
  towerS : (β : V ℓ) → IsOrd β → S
  towerS β ob = LsetS β ob

  towerS-fst : (β : V ℓ) (ob : IsOrd β) → fst (towerS β ob) ≡ Lset β
  towerS-fst β ob = refl

  powS : (β : V ℓ) → IsOrd β → S
  powS β ob = 𝒟ₒS β ob

  powS-fst : (β : V ℓ) (ob : IsOrd β) → fst (powS β ob) ≡ 𝒟ₒ (Lset β)
  powS-fst β ob = refl
```

<!--en-->
## The description

Six binders, in the order in which each one's condition can be stated. The first
binds the **tower** at the slot `d`, reached the only way the hierarchy can be
reached, through the sequence chapter's graph. The second binds its **definable
subsets** through the powerset chapter's `DefAt`{.Agda}, and the two compared sets
are required to lie in it: that is how the step's two membership components are
obtained, since a member of the next stage is exactly a definable subset of this
one, and no separate lemma is needed. The third binds the **table's value** at `d`,
said as an application of the slot `f`, which is what makes the description read
against whatever table the caller holds rather than against a named one. The
fourth binds the **code set** over the tower through the previous chapter's
`CodesAt`{.Agda}, which was written for exactly this slot.

The last two binders pin constants by an object equality, because the internalized
step takes seven **slots** and a slot holds a variable: the order on the codes,
and the code set at the empty alphabet, which is the one that says a skeleton is
parameter-free. Both are particular sets of the model, both are already sealed
where they were built, and pinning them costs one conjunct each.

The whole formula is sealed. It is read at constants downstream, and that is the
law the family chapter measured at 376 s against 3.8 s.
<!--zh-->
## 那条描述

六个绑定，其次序恰是每一条条件能被陈述出来的次序。第一个绑定槽位 `d` 处的**塔**，抵达它的办法是抵达层级的唯一办法，即经序列那一章的图。第二个经幂集那一章的 `DefAt`{.Agda} 绑定它的**可定义子集**，并要求被比较的那两个集合落在其中：那一步的两个隶属分量正是这样得到的，因为下一个阶段的成员恰恰就是这一个阶段的可定义子集，无须另立引理。第三个绑定表在 `d` 处的**取值**，说成槽位 `f` 的一次应用，正是这一点使那条描述读在调用方所持的任意一张表上、而不是读在某张被点名的表上。第四个经上一章的 `CodesAt`{.Agda} 绑定塔之上的**码集**，而那条描述当初就是为这个槽位写的。

最后两个绑定用对象等词钉住常量，因为已内化的那一步取七个**槽位**，而槽位持有的是变元：诸码之上的序，以及空字母表处的码集，后者正是说出一个骨架无参的那一个。二者都是模型的特定集合，二者在被造出之处都已封印，钉住它们各花一个合取项。

整条公式被封印。它在下游被读在诸常元上，而那正是族那一章实测为 376 秒对 3.8 秒的定律。
<!--/-->

```agda
-- perf: the description is read at constants, so it is sealed where it is built
opaque
  Stp : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  Stp d f u v =
    ∃̇ ( LsetGraphAt zero (suc d)
      ∧̇ ∃̇ ( DefAt zero (suc zero)
           ∧̇ ( (var (sh2 u) ∈̇ var zero)
             ∧̇ ( (var (sh2 v) ∈̇ var zero)
               ∧̇ ∃̇ ( appAt (sh3 f) (sh3 d) zero
                    ∧̇ ∃̇ ( CodesAt zero (sh3 zero)
                         ∧̇ ∃̇ ( (var zero ≐ con codeOrder)
                              ∧̇ ∃̇ ( (var zero ≐ con (AllCodes ∅ʟ))
                                   ∧̇ StepAt iOrd iRel iTow iCod iNil
                                       (sh6 u) (sh6 v) ) ) ) ) ) ) ) )
```

<!--en-->
## The six binders, layer by layer

Six existential binders under conjunctions unfold into six nested truncations, and
the two readings walk that nesting in opposite directions. Each layer gets a name,
`One`{.Agda} through `Six`{.Agda}, so that neither reading ever writes the nesting
out and every truncation payload is named, which is the standing law for payloads.

`StepHolds`{.Agda} is the innermost layer, the satisfaction of the internalized
step at the six bound elements, and it is **sealed**. That is a law measured here
for the first time, and it is the difference between this chapter finishing and
not finishing. The step adequacy is proved on a frame generic in those elements;
instantiating that frame at the concrete elements this description binds forces
the frame's conclusion type to be normalized, and unsealed it does not finish
(over 200 s, against 7 s for the whole chapter with the seal). The rule is the
same one the descriptions themselves obey, applied one level up: **the type a
frame concludes in is sealed where it is built**.
<!--zh-->
## 六个绑定，逐层展开

合取之下的六个存在绑定展开成六层嵌套的截断，而那两条读式沿相反方向走这层嵌套。每一层都取一个名字，从 `One`{.Agda} 到 `Six`{.Agda}，于是两条读式都不必把嵌套写开，且每个截断载荷都有名字，而那是关于载荷的常设定律。

`StepHolds`{.Agda} 是最里面那一层，即已内化的那一步在那六个被绑定的元素处的满足关系，而它被**封印**。这是本章头一回实测出的一条定律，也正是本章跑得完与跑不完之别。那一步的充分性是在一个对那些元素保持通用的框架上证出的；把那个框架实例化到本描述所绑定的具体元素上，会迫使那个框架的结论类型被正规化，而不封印时它跑不完 (超过 200 秒，对全章封印后的 7 秒)。这条规矩与诸描述自身所守的是同一条，只是被施用在高一层：**一个框架所结论于其中的类型，要在它被造出之处封印**。
<!--/-->

```agda
module Reading {n : ℕ} (d f u v : Fin n) (γ : S ^ n)
               (od : IsOrd (fst (lookup d γ))) where
  private
    δ : V ℓ
    δ = fst (lookup d γ)

    ordW : SWO ⟪ Lset δ ⟫
    ordW = carry (Lset δ) (orderAt δ od)

    module NM = Naming (Lset δ) ordW

    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ)) ∥₁

    -- perf: the type the step adequacy concludes in is sealed where it is built;
    -- unsealed, instantiating the frame at the concrete elements this description
    -- binds does not finish (over 200 s against 7 s for the whole chapter)
    opaque
      StepHolds : (tw pw rl cs ro c0 : S) → Type (ℓ-suc ℓ)
      StepHolds tw pw rl cs ro c0 =
        ⟨ (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ)
          ⊨ StepAt iOrd iRel iTow iCod iNil (sh6 u) (sh6 v) ⟩

    Six : (tw pw rl cs ro c0 : S) → Type (ℓ-suc ℓ)
    Six tw pw rl cs ro c0 =
        ⟨ (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ (var zero ≐ con (AllCodes ∅ʟ)) ⟩
      × StepHolds tw pw rl cs ro c0

    Five : (tw pw rl cs ro : S) → Type (ℓ-suc ℓ)
    Five tw pw rl cs ro =
        ⟨ (ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ (var zero ≐ con codeOrder) ⟩
      × ∥ (Σ[ c0 ∈ S ] Six tw pw rl cs ro c0) ∥₁

    Four : (tw pw rl cs : S) → Type (ℓ-suc ℓ)
    Four tw pw rl cs =
        ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
      × ∥ (Σ[ ro ∈ S ] Five tw pw rl cs ro) ∥₁

    Three : (tw pw rl : S) → Type (ℓ-suc ℓ)
    Three tw pw rl =
        ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
      × ∥ (Σ[ cs ∈ S ] Four tw pw rl cs) ∥₁

    Two : (tw pw : S) → Type (ℓ-suc ℓ)
    Two tw pw =
        ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      × ( ⟨ fst (lookup u γ) ∈ fst pw ⟩
        × ( ⟨ fst (lookup v γ) ∈ fst pw ⟩
          × ∥ (Σ[ rl ∈ S ] Three tw pw rl) ∥₁ ) )

    One : (tw : S) → Type (ℓ-suc ℓ)
    One tw = ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
           × ∥ (Σ[ pw ∈ S ] Two tw pw) ∥₁
```

<!--en-->
## The step adequacy at a stage

`Slots`{.Agda} is where all six arguments of the step adequacy are supplied, and
it is generic in the six sets, each carrying its defining equation as a
hypothesis. The carrier is the tower at the stage and the well-order on it is the
one this part's family gives there; the code side is filled by the limit chapter's
order and its two representation lemmas, which the family chapter made
unconditional; the parameter side is filled by the table's readings at the value
the description binds, which is where the step parameter's own hypothesis is
spent. The remaining five arguments are the equations pinning the five slots, and
nothing else is used.

What comes out is two readings of the innermost layer and, on either side of them,
the two translations between the frame's spelling of "is the least name of" and
the step chapter's exported predicate. The translations are only `sym`{.Agda} on
each of two components, but they are placed **here**, where the name is still a
variable, and not at the call sites, where it is the value of the least-name
search.
<!--zh-->
## 阶段处的那一步之充分性

`Slots`{.Agda} 是那一步的充分性的全部六个实参被供给之处，而它对那六个集合保持通用，每一个都带着自己的定义方程作为假设。载体是阶段处的塔，其上的良序就是本部那一族在那里给出的那个；码那一侧由极限那一章的序连同它的两条表示引理填上，而那两条已被族那一章做成无条件的；参数那一侧由表在描述所绑定的那个取值处的诸读式填上，而这正是步进参数自己那条假设被花掉之处。其余五个实参是钉住五个槽位的那些等式，此外别无所用。

出来的是最里那一层的两条读式，以及在它们两侧、框架对「是最小名字」的写法与步进那一章所导出的谓词之间的两次翻译。那两次翻译不过是在两个分量上各作一次 `sym`{.Agda}，但它们被安置在**此处**，即名字仍是变元之处，而不是安置在调用处，即名字是最小名字搜寻之取值之处。
<!--/-->

```agda
  module Slots (tw pw rl cs ro c0 : S)
               (qtw : fst tw ≡ Lset δ)
               (hrel : IsRel δ rl)
               (qcs : fst cs ≡ fst (AllCodes (LsetS δ od)))
               (qro : fst ro ≡ fst codeOrder)
               (qc0 : fst c0 ≡ fst (AllCodes ∅ʟ)) where
    private
      module A6 = At (Lset δ) (snd (LsetS δ od)) ordW
      module L6 = A6.Least codeOrder rl codeOrder-rep codeOrder-fill
                    (ixRel-rep δ od rl hrel) (ixRel-fill δ od rl hrel)
      module St = L6.Step iOrd iRel iTow iCod iNil (sh6 u) (sh6 v)
        (c0 ∷ ro ∷ cs ∷ rl ∷ pw ∷ tw ∷ γ)
        qro refl (Σ≡Prop (λ x → snd (isL x)) qtw) qcs qc0

    LeastFst : NM.Name → Type (ℓ-suc ℓ)
    LeastFst = St.LeastOf (sh6 u)

    LeastSnd : NM.Name → Type (ℓ-suc ℓ)
    LeastSnd = St.LeastOf (sh6 v)

    leastFst-in : (t : NM.Name)
                → IsLeastName δ ordW t (fst (lookup u γ)) → LeastFst t
    leastFst-in t (q , mn) = sym q , λ t' q' → mn t' (sym q')

    leastSnd-in : (t : NM.Name)
                → IsLeastName δ ordW t (fst (lookup v γ)) → LeastSnd t
    leastSnd-in t (q , mn) = sym q , λ t' q' → mn t' (sym q')

    leastFst-out : (t : NM.Name)
                 → LeastFst t → IsLeastName δ ordW t (fst (lookup u γ))
    leastFst-out t (q , mn) = sym q , λ t' q' → mn t' (sym q')

    leastSnd-out : (t : NM.Name)
                 → LeastSnd t → IsLeastName δ ordW t (fst (lookup v γ))
    leastSnd-out t (q , mn) = sym q , λ t' q' → mn t' (sym q')

    opaque
      unfolding StepHolds

      holds-in : (t₁ t₂ : NM.Name) → LeastFst t₁ → LeastSnd t₂ → NM._≺ₙ_ t₁ t₂
               → StepHolds tw pw rl cs ro c0
      holds-in = St.StepAt-fill

      holds-out : StepHolds tw pw rl cs ro c0
                → ∥ Σ[ t₁ ∈ NM.Name ] Σ[ t₂ ∈ NM.Name ]
                      (LeastFst t₁ × (LeastSnd t₂ × NM._≺ₙ_ t₁ t₂)) ∥₁
      holds-out = St.StepAt-read
```

<!--en-->
## Unpacking

`atAll`{.Agda} takes the six sets and everything the six binders held, and returns
the meta step. The tower's graph pins the first set to the tower, the definable
subsets' description pins the second to the definable subsets of it, and those two
equations together turn the two membership conjuncts into memberships of the next
stage, which is what the meta step's two components are. The application at `f`
turns into a pair in the table, which is what the step parameter's hypothesis
consumes, and it is consumed at **whatever value the description bound**, not at
one the caller chose: that is why the hypothesis quantifies over every value the
table records there. The code set reading pins the fourth, and the two pinned
constants are already equations. Then the frame's reading gives two names, least
for the two sets, with the naming comparison between them, and the step chapter's
own reading turns that into the comparison at the stage.
<!--zh-->
## 拆开

`atAll`{.Agda} 取那六个集合与六个绑定所持有的一切，交回元层面的那一步。塔的图把第一个集合钉在塔上，可定义子集那条描述把第二个钉在它的可定义子集上，而这两条等式合起来把两个隶属合取项变成对下一个阶段的隶属，那正是元层面那一步的两个分量。`f` 处的应用变成表中的一个对，那正是步进参数那条假设所消费的东西，且它是在**描述所绑定的那个取值**处被消费的，而不是在调用方所选的某个取值处：这正是那条假设为何要对表在那里记录的每一个取值作全称。码集那条读式钉住第四个，而被钉住的两个常量本身就是等式。随后，框架的读式给出两个名字，即那两个集合各自的最小名字，连同它们之间的命名比较，而步进那一章自己的读式把它变成阶段处的那次比较。
<!--/-->

```agda
  private
    atAll : (tw pw rl cs ro c0 : S)
          → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
          → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
          → ⟨ fst (lookup u γ) ∈ fst pw ⟩
          → ⟨ fst (lookup v γ) ∈ fst pw ⟩
          → ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
          → ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
          → ((r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r)
          → fst ro ≡ fst codeOrder
          → fst c0 ≡ fst (AllCodes ∅ʟ)
          → StepHolds tw pw rl cs ro c0 → Goal
    atAll tw pw rl cs ro c0 hg hdef hu hv happ hcs vals qro qc0 hstep =
      PT.map atNames (K.holds-out hstep)
      where
      qtw : fst tw ≡ Lset δ
      qtw = Lset-only zero (suc d) (tw ∷ γ) hg od

      qpw : fst pw ≡ 𝒟ₒ (Lset δ)
      qpw = subst ⟨_⟩ (DefAt-stage δ od zero (suc zero) (pw ∷ tw ∷ γ) qtw) hdef

      inSuc : (x : V ℓ) → ⟨ x ∈ fst pw ⟩ → ⟨ x ∈ Lset (sucV δ) ⟩
      inSuc x h = subst (λ z → ⟨ x ∈ z ⟩) (sym (Lset-suc δ))
        (subst (λ z → ⟨ x ∈ z ⟩) qpw h)

      a : New δ
      a = fst (lookup u γ) , inSuc (fst (lookup u γ)) hu

      b : New δ
      b = fst (lookup v γ) , inSuc (fst (lookup v γ)) hv

      hrel : IsRel δ rl
      hrel = vals rl
        (subst ⟨_⟩ (appAt-adequate (sh3 f) (sh3 d) zero (rl ∷ pw ∷ tw ∷ γ)) happ)

      qcs : fst cs ≡ fst (AllCodes (LsetS δ od))
      qcs = cong fst (CodesAt-out (LsetS δ od) zero (sh3 zero)
              (cs ∷ rl ∷ pw ∷ tw ∷ γ) qtw hcs)

      module K = Slots tw pw rl cs ro c0 qtw hrel qcs qro qc0

      atNames : Σ[ t₁ ∈ NM.Name ] Σ[ t₂ ∈ NM.Name ]
                  ( K.LeastFst t₁ × ( K.LeastSnd t₂ × NM._≺ₙ_ t₁ t₂ ) )
              → Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ))
      atNames (t₁ , (t₂ , (l₁ , (l₂ , lt)))) =
          a .snd
        , ( b .snd
          , stepAt-fill δ ordW a b t₁ t₂
              (K.leastFst-out t₁ l₁) (K.leastSnd-out t₂ l₂) lt )
```

<!--en-->
## Packing

The other direction chooses the six sets and discharges the six conditions. The
tower and its definable subsets are the sealed elements, and their conditions are
the sequence chapter's "this is the tower" and the powerset chapter's "this is
the definable subsets of it", each read off a single equation. The table's value
is the one the caller hands over, and the code set is the one the previous
chapter's description carves, so its condition is that description read at the
tower. The two constants are pinned by `refl`{.Agda}, because the element bound is
the constant itself. The innermost conjunct is the frame's other reading, applied
to the two least names the step chapter's search returns, and to the naming
comparison the step chapter reads off the comparison at the stage.
<!--zh-->
## 装回

另一个方向选定那六个集合并交割那六条条件。塔与它的可定义子集就是那两个被封印的元素，它们的条件是序列那一章的「这是那座塔」与幂集那一章的「这是它的可定义子集」，各由一条等式读出。表的取值是调用方交来的那一个，码集则是上一章那条描述所雕出的那一个，故它的条件就是那条描述读在那座塔上。两个常量由 `refl`{.Agda} 钉住，因为被绑定的元素就是那个常量本身。最里面那个合取项是框架的另一条读式，施于步进那一章的搜寻交回的两个最小名字，以及步进那一章由阶段处的比较读出的那次命名比较。
<!--/-->

```agda
  module Pack (rl : S) (hpr : ⟨ pr δ (fst rl) ∈ fst (lookup f γ) ⟩)
              (hrel : IsRel δ rl)
              (hx : ⟨ fst (lookup u γ) ∈ Lset (sucV δ) ⟩)
              (hy : ⟨ fst (lookup v γ) ∈ Lset (sucV δ) ⟩)
              where
    private
      module K = Slots (towerS δ od) (powS δ od) rl (AllCodes (LsetS δ od))
                   codeOrder (AllCodes ∅ʟ) (towerS-fst δ od) hrel refl refl refl

      a : New δ
      a = fst (lookup u γ) , hx

      b : New δ
      b = fst (lookup v γ) , hy

      n₁ : Σ[ t ∈ NM.Name ] IsLeastName δ ordW t (fst (lookup u γ))
      n₁ = leastNameOf δ ordW a

      n₂ : Σ[ t ∈ NM.Name ] IsLeastName δ ordW t (fst (lookup v γ))
      n₂ = leastNameOf δ ordW b

      hg : ⟨ (towerS δ od ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
      hg = Lset-defines zero (suc d) (towerS δ od ∷ γ) od (towerS-fst δ od)

      hdef : ⟨ (powS δ od ∷ towerS δ od ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      hdef = subst ⟨_⟩
        (sym (DefAt-stage δ od zero (suc zero)
                (powS δ od ∷ towerS δ od ∷ γ) (towerS-fst δ od)))
        (powS-fst δ od)

      inPow : (x : V ℓ) → ⟨ x ∈ Lset (sucV δ) ⟩ → ⟨ x ∈ fst (powS δ od) ⟩
      inPow x h = subst (λ z → ⟨ x ∈ z ⟩) (sym (powS-fst δ od))
        (subst (λ z → ⟨ x ∈ z ⟩) (Lset-suc δ) h)

      happ : ⟨ (rl ∷ powS δ od ∷ towerS δ od ∷ γ)
              ⊨ appAt (sh3 f) (sh3 d) zero ⟩
      happ = subst ⟨_⟩
        (sym (appAt-adequate (sh3 f) (sh3 d) zero
                (rl ∷ powS δ od ∷ towerS δ od ∷ γ))) hpr

      hcs : ⟨ (AllCodes (LsetS δ od) ∷ rl ∷ powS δ od ∷ towerS δ od ∷ γ)
             ⊨ CodesAt zero (sh3 zero) ⟩
      hcs = CodesAt-in (LsetS δ od) zero (sh3 zero)
        (AllCodes (LsetS δ od) ∷ rl ∷ powS δ od ∷ towerS δ od ∷ γ)
        (towerS-fst δ od) refl

      hstep : relOf (stepOrder δ od) a b
            → StepHolds (towerS δ od) (powS δ od) rl (AllCodes (LsetS δ od))
                codeOrder (AllCodes ∅ʟ)
      hstep cmp = K.holds-in (n₁ .fst) (n₂ .fst)
        (K.leastFst-in (n₁ .fst) (n₁ .snd)) (K.leastSnd-in (n₂ .fst) (n₂ .snd))
        (stepAt-read δ ordW a b (n₁ .fst) (n₂ .fst) (n₁ .snd) (n₂ .snd) cmp)

    packAll : relOf (stepOrder δ od) a b → ∥ (Σ[ tw ∈ S ] One tw) ∥₁
    packAll cmp =
      ∣ towerS δ od
      , ( hg
        , ∣ powS δ od
          , ( hdef
            , ( inPow (fst (lookup u γ)) hx
              , ( inPow (fst (lookup v γ)) hy
                , ∣ rl
                  , ( happ
                    , ∣ AllCodes (LsetS δ od)
                      , ( hcs
                        , ∣ codeOrder
                          , ( refl
                            , ∣ AllCodes ∅ʟ
                              , ( refl , hstep cmp ) ∣₁ ) ∣₁ ) ∣₁ ) ∣₁ ) ) ) ∣₁ ) ∣₁
```

<!--en-->
## The two readings

Only here is the seal opened, and only for the two readings, which peel the six
layers by named helpers, one per layer, each with its conclusion written down. No
`with`{.Agda} appears: a case split concluding in a satisfaction is a named helper
with its conclusion written down, and that is the law the faithfulness chapter
measured past 300 s. The exported `stp-out`{.Agda} and `stp-in`{.Agda} are the two
readings at the exact types the frame demands, and they carry the frame's own
asymmetry: soundness quantifies over every value the table records at the carrier,
because the description it reads may have bound a value of its own, while
completeness takes the single value the caller realizes with.
<!--zh-->
## 两条读式

只有到这里才打开那道封印，且只为那两条读式打开。它们按层剥开那六层，每层一个具名辅助，每一个都把自己的结论写下来。全篇不出现 `with`{.Agda}：一次结论落在满足关系上的分情形必须是把结论写下来的具名辅助，而那是忠实那一章实测超过 300 秒的定律。导出的 `stp-out`{.Agda} 与 `stp-in`{.Agda} 就是那两条读式，其类型正是框架所索取的，且它们承接了框架自身的那份不对称：可靠性对表在该载体处记录的每一个取值作全称，因为它所读的那条描述可能自己绑定了一个取值；而完备性取的是调用方据以实现的那单个取值。
<!--/-->

```agda
  opaque
    unfolding Stp StepHolds

    read : ((r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r)
         → ⟨ γ ⊨ Stp d f u v ⟩ → Goal
    read vals = PT.rec PT.squash₁ atOne
      where
      atSix : (tw pw rl cs ro c0 : S)
            → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
            → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
            → ⟨ fst (lookup u γ) ∈ fst pw ⟩
            → ⟨ fst (lookup v γ) ∈ fst pw ⟩
            → ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
            → ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
            → fst ro ≡ fst codeOrder
            → Six tw pw rl cs ro c0 → Goal
      atSix tw pw rl cs ro c0 hg hdef hu hv happ hcs qro (qc0 , hstep) =
        atAll tw pw rl cs ro c0 hg hdef hu hv happ hcs vals qro qc0 hstep

      atFive : (tw pw rl cs ro : S)
             → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
             → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
             → ⟨ fst (lookup u γ) ∈ fst pw ⟩
             → ⟨ fst (lookup v γ) ∈ fst pw ⟩
             → ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
             → ⟨ (cs ∷ rl ∷ pw ∷ tw ∷ γ) ⊨ CodesAt zero (sh3 zero) ⟩
             → Five tw pw rl cs ro → Goal
      atFive tw pw rl cs ro hg hdef hu hv happ hcs (qro , h) =
        PT.rec PT.squash₁
          (λ { (c0 , hsix) →
                 atSix tw pw rl cs ro c0 hg hdef hu hv happ hcs qro hsix }) h

      atFour : (tw pw rl cs : S)
             → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
             → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
             → ⟨ fst (lookup u γ) ∈ fst pw ⟩
             → ⟨ fst (lookup v γ) ∈ fst pw ⟩
             → ⟨ (rl ∷ pw ∷ tw ∷ γ) ⊨ appAt (sh3 f) (sh3 d) zero ⟩
             → Four tw pw rl cs → Goal
      atFour tw pw rl cs hg hdef hu hv happ (hcs , h) =
        PT.rec PT.squash₁
          (λ { (ro , hfive) →
                 atFive tw pw rl cs ro hg hdef hu hv happ hcs hfive }) h

      atThree : (tw pw rl : S)
              → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
              → ⟨ (pw ∷ tw ∷ γ) ⊨ DefAt zero (suc zero) ⟩
              → ⟨ fst (lookup u γ) ∈ fst pw ⟩
              → ⟨ fst (lookup v γ) ∈ fst pw ⟩
              → Three tw pw rl → Goal
      atThree tw pw rl hg hdef hu hv (happ , h) =
        PT.rec PT.squash₁
          (λ { (cs , hfour) →
                 atFour tw pw rl cs hg hdef hu hv happ hfour }) h

      atTwo : (tw pw : S) → ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
            → Two tw pw → Goal
      atTwo tw pw hg (hdef , (hu , (hv , h))) =
        PT.rec PT.squash₁
          (λ { (rl , hthree) → atThree tw pw rl hg hdef hu hv hthree }) h

      atOne : Σ[ tw ∈ S ] One tw → Goal
      atOne (tw , (hg , h)) =
        PT.rec PT.squash₁ (λ { (pw , htwo) → atTwo tw pw hg htwo }) h

    fill : (r : S) → ⟨ pr δ (fst r) ∈ fst (lookup f γ) ⟩ → IsRel δ r
         → Under δ (stepOrder δ od) (fst (lookup u γ)) (fst (lookup v γ))
         → ⟨ γ ⊨ Stp d f u v ⟩
    fill r hpr hrel (hx , (hy , cmp)) = Pack.packAll r hpr hrel hx hy cmp
```

```agda
stp-out : ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
        → ((r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
           → IsRel (fst (lookup d γ)) r)
        → ⟨ γ ⊨ Stp d f u v ⟩
        → ∥ Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
              (fst (lookup u γ)) (fst (lookup v γ)) ∥₁
stp-out = Reading.read

stp-in : ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
       → (r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
       → IsRel (fst (lookup d γ)) r
       → Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
           (fst (lookup u γ)) (fst (lookup v γ))
       → ⟨ γ ⊨ Stp d f u v ⟩
stp-in = Reading.fill
```

<!--en-->
## The frame opened

One line. It supplies the frame's last parameter, and with it the whole of the
order table becomes unconditional. Said plainly, the following now hold with no
hypothesis beyond this part's standing one, excluded middle:

- from `L.Choice.Faithful`{.Agda}: `CondCore`{.Agda} with its two readings,
  `Cond`{.Agda}, `Cond₀`{.Agda}, `cond-spec`{.Agda} and `cond₀-spec`{.Agda}, that
  is, the order at a stage completely described, in both the forms the table's
  construction asks for;
- from `L.Choice.Table`{.Agda}: the step condition `StepAt`{.Agda} with
  `step-rel`{.Agda} and `step-table`{.Agda}; the approximation `ApproxAt`{.Agda}
  and the graph `GraphAt`{.Agda} with their readings, `approx-val`{.Agda} and
  `approx-uniq`{.Agda}, `graph-only`{.Agda} and `graph-table`{.Agda};
  `PairGraphAt`{.Agda}; `Recorded`{.Agda}, `IsTable`{.Agda}, `Bundle`{.Agda},
  `table-out`{.Agda}, `table-in`{.Agda} and `bound`{.Agda}; the construction
  `tableAt`{.Agda} itself; and the relation it carries at every ordinal,
  `relL`{.Agda} and `relL-spec`{.Agda}, with all four representation lemmas
  `relL-fill`{.Agda}, `relL-rep`{.Agda}, `ix-fill`{.Agda} and `ix-rep`{.Agda}.

This was checked the way the re-cut checked its own claim: the results were
imported into a throwaway module assuming nothing but excluded middle, each
restated at its type spelled out by hand, and used to derive that the order at the
bounding ordinal is an element of the model whose membership is irreflexive. The
probe was then deleted.
<!--zh-->
## 框架被打开

一行。它供给那个框架的最后一个参数，随之，整张序之表变成无条件的。说白了，以下诸条如今在本部那条常设假设 (排中律) 之外不带任何假设即成立：

- 出自 `L.Choice.Faithful`{.Agda}：`CondCore`{.Agda} 连同它的两条读式、`Cond`{.Agda}、`Cond₀`{.Agda}、`cond-spec`{.Agda} 与 `cond₀-spec`{.Agda}，亦即阶段处的序被完整描述出来，且以表的构造所索取的两种形式给出；
- 出自 `L.Choice.Table`{.Agda}：步进条件 `StepAt`{.Agda} 连同 `step-rel`{.Agda} 与 `step-table`{.Agda}；逼近 `ApproxAt`{.Agda} 与图 `GraphAt`{.Agda} 连同它们的诸读式、`approx-val`{.Agda} 与 `approx-uniq`{.Agda}、`graph-only`{.Agda} 与 `graph-table`{.Agda}；`PairGraphAt`{.Agda}；`Recorded`{.Agda}、`IsTable`{.Agda}、`Bundle`{.Agda}、`table-out`{.Agda}、`table-in`{.Agda} 与 `bound`{.Agda}；构造 `tableAt`{.Agda} 自身；以及它在每个序数处所携带的那个关系，即 `relL`{.Agda} 与 `relL-spec`{.Agda}，连同全部四条表示引理 `relL-fill`{.Agda}、`relL-rep`{.Agda}、`ix-fill`{.Agda} 与 `ix-rep`{.Agda}。

这一点是按重切验证它自己那条主张的办法验证的：把诸结果引入一个除排中律外不假设任何东西的临时模块，逐条按手写出来的类型重述，再用它们推出「上界序数处的序是模型的一个元素，且其隶属是非自反的」。那个探针随后被删除。
<!--/-->

```agda
open Ordered Stp stp-out stp-in public
```

<!--en-->
## The order at the bounding ordinal

The last chapter will want one particular instance, in one particular shape. Given
a set of `L`, the stage chapter's bounding ordinal is an ordinal above that set's
own stage, hence above its members and their members, and above `ω` as well. It is
constructible, because an ordinal appears at the stage after itself. So the family
has an order on the members of the tower there, and the table has that order as an
**element of the model**, with the two representation lemmas reading membership in
that element against the meta comparison in both directions. That triple, the
element and its two lemmas, is what a separation will be run against.
<!--zh-->
## 上界序数处的序

最后一章要的是一个特定的实例，且要一个特定的形状。给定 `L` 的一个集合，阶段那一章的上界序数是一个高于该集合自身阶段的序数，从而高于它的成员及其成员，也高于 `ω`。它是可构造的，因为一个序数现身于自身之后的那个阶段。于是那一族在那里的塔的诸成员上有一个序，而表把那个序作为**模型的一个元素**握在手里，两条表示引理则把对该元素的隶属与元层面的比较双向读通。这个三元组，即那个元素与它的两条引理，正是一次分离将要据以施行的东西。
<!--/-->

```agda
module Bound (a : V ℓ) (p : ⟨ isL a ⟩) where
  boundOrd : V ℓ
  boundOrd = stageBound a p .fst

  boundOrd-ord : IsOrd boundOrd
  boundOrd-ord = stageBound a p .snd .fst

  boundOrd-isL : ⟨ isL boundOrd ⟩
  boundOrd-isL = Lset→isL (sucV boundOrd) (suc-ord boundOrd-ord) boundOrd
    (ord∈Lset-suc boundOrd boundOrd-ord)

  boundOrder : SWO (Mem (Lset boundOrd))
  boundOrder = orderAt boundOrd boundOrd-ord

  orderL : S
  orderL = relL boundOrd boundOrd-isL boundOrd-ord

  orderL-fill : (x y : Mem (Lset boundOrd)) → relOf boundOrder x y
              → ⟨ pr (fst x) (fst y) ∈ fst orderL ⟩
  orderL-fill = relL-fill boundOrd boundOrd-isL boundOrd-ord

  orderL-rep : (x y : Mem (Lset boundOrd))
             → ⟨ pr (fst x) (fst y) ∈ fst orderL ⟩ → relOf boundOrder x y
  orderL-rep = relL-rep boundOrd boundOrd-isL boundOrd-ord
```

<!--en-->
## Recap

`Stp`{.Agda} is the step described: a **sealed** formula binding six sets and
pinning two constants. The six are the tower at the stage, reached through the
sequence chapter's graph; its definable subsets, reached through the powerset
chapter's `DefAt`{.Agda}, with the two compared sets required to lie in it, which
is how the step's two membership components arrive without a lemma nobody has; the
table's value at the stage, reached as an application, which is what keeps the
description reading against whatever table the caller holds; and the code set over
the tower, reached through the previous chapter's `CodesAt`{.Agda}, which was
written for this slot. The two pinned by an object equality are the order on the
codes and the code set at the empty alphabet, because a slot holds a variable and
those two are particular sets. The body at those seven slots is the internalized
step.

`Reading.read`{.Agda} and `Reading.fill`{.Agda} are unpack and pack over the six
binders, and `stp-out`{.Agda} and `stp-in`{.Agda} are those two at the frame's
types. `Slots`{.Agda} is where the step adequacy is supplied its six arguments,
generic in the six sets with their equations as hypotheses: the code side from the
limit and family chapters, unconditional; the carrier side from the table's
readings at the bound value, which is the step parameter's own hypothesis and the
only input this chapter takes from outside.

One measurement, and it is a law at a new place: **the type a frame concludes in
is sealed where it is built**. `StepHolds`{.Agda} is the step adequacy's
conclusion; instantiating the frame at the concrete elements this description
binds normalizes it, and unsealed that does not finish (over 200 s, against 7 s
for the whole chapter). Two inherited laws are obeyed without new measurement: the
elements reaching the slots are sealed, and the description itself is sealed
because it is read at constants.

`open Ordered`{.Agda} is the one line, and with it the order table is
unconditional: the construction and all four of its readings, together with
everything the two frames export. `Bound`{.Agda} is the shape the last chapter
separates with: the bounding ordinal of a set of `L`, the order on the members of
the tower there as an element of the model, and its two representation lemmas.
<!--zh-->
## 小结

`Stp`{.Agda} 是被描述出来的那一步：一条**被封印**的公式，绑定六个集合并钉住两个常量。六个是：阶段处的塔，经序列那一章的图抵达；它的可定义子集，经幂集那一章的 `DefAt`{.Agda} 抵达，并要求被比较的那两个集合落在其中，那一步的两个隶属分量就是这样到场的，而不必动用谁也没有的一条引理；表在该阶段的取值，说成一次应用抵达，正是这一点使那条描述始终读在调用方所持的任意一张表上；以及塔之上的码集，经上一章的 `CodesAt`{.Agda} 抵达，而那条描述就是为这个槽位写的。用对象等词钉住的两个是诸码之上的序与空字母表处的码集，因为槽位持有变元，而那两样是特定的集合。落在那七个槽位上的主体就是已内化的那一步。

`Reading.read`{.Agda} 与 `Reading.fill`{.Agda} 是对那六个绑定的拆开与装回，而 `stp-out`{.Agda} 与 `stp-in`{.Agda} 就是这两条落在框架所要类型上的样子。`Slots`{.Agda} 是那一步的充分性被供给六个实参之处，对那六个集合保持通用、以它们的等式为假设：码那一侧来自极限与族两章，无条件；载体那一侧来自表在所绑定取值处的诸读式，而那正是步进参数自己的假设，也是本章从外面取的唯一输入。

一次实测，且是一条定律在新地方的现身：**一个框架所结论于其中的类型，要在它被造出之处封印**。`StepHolds`{.Agda} 就是那一步充分性的结论；把那个框架实例化到本描述所绑定的具体元素上会把它正规化，而不封印时那件事跑不完 (超过 200 秒，对全章的 7 秒)。另有两条承袭而来的定律无须新实测即被遵守：抵达诸槽位的元素被封印，而那条描述自身被封印，因为它被读在诸常元上。

`open Ordered`{.Agda} 就是那一行，随之，序之表变成无条件的：那个构造连同它的全部四条读式，以及两个框架所导出的一切。`Bound`{.Agda} 是最后一章据以分离的那个形状：`L` 的一个集合的上界序数、那里的塔的诸成员上的序作为模型的一个元素，以及它的两条表示引理。
<!--/-->
