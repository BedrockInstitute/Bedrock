# Reflecting a whole formula

<!--en-->
The previous chapter reflected one quantifier. A formula has many, and the aim is
to tighten all of them at once: to find a stage at which every unbounded
quantifier of a given formula may be read as ranging over that stage only,
without changing the formula's truth in L. That is exactly what relativization
names, so the statement is that a formula and its relativization to the stage
agree, and since a relativization is Δ₀, the effect is to trade an arbitrary
formula for a bounded one at the cost of naming a stage.

The proof is structural induction, and it needs two things of the stage. At an
unbounded quantifier it needs the previous chapter's closure, for the quantifier's
own matrix. At a bounded quantifier it needs the bound to lie in the stage, so
that anything the bound admits does too; that is the constants condition the
separation chapter already knows how to meet.

No single-matrix limit can serve all the matrices at once, because closure is not
inherited by larger stages: enlarging the stage admits more environments to
answer for. So the ladder is built jointly. One rung's step merges, over the
formula's structure, the single-matrix step of every matrix in it, together with
the stage holding the constants. The limit then answers for every matrix, and the
previous chapter's argument applies to each without being run again.
<!--zh-->
上一章反射了一个量词。一条公式有许多个，而目标是一举收紧它们全部：找到一个阶段，使给定公式的每个无界量词都可读作只在该阶段上取值，而不改变该公式在 L 中的真值。这恰是相对化所命名的东西，故所要陈述的是：公式与它到该阶段的相对化彼此一致；而相对化是 Δ₀ 的，效果便是以点名一个阶段为代价，把任意公式换成有界公式。

证明是结构归纳，它向那个阶段索取两样东西。在无界量词处，它索取上一章的闭包，针对该量词自己的矩阵。在有界量词处，它索取那个界落在该阶段里，好让界所准入的一切也落在其中；那正是分离那一章早已懂得如何满足的常元条件。

没有哪个单矩阵极限能同时服务全部矩阵，因为闭包不为更大的阶段所继承：把阶段扩大，就有更多环境等着它作答。故这架梯是联合造的。一级的步进沿公式的结构，把其中每个矩阵的单矩阵步进合并起来，连同装着常元的那个阶段。于是极限为每个矩阵作答，而上一章的论证施于每一个，都无须重跑。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.ReflectFo {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Bounding using ( BoundedTm; BoundedFo )
open import FOL.Manipulation.Relativize using ( relativize; module Correct )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( ∅-ord; bound2 )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL )
open import L.Axioms.Separation {ℓ} lem
  using ( Below′; liftFoTo; mkBoundedFo )
open import L.Reflect {ℓ} lem
  using ( Below; LsetEnv; pickStage; ClosedFor; module Ladder; module Single )

open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )
```

<!--en-->
## The stage as an element
<!--zh-->
## 作为元素的阶段
<!--/-->

<!--en-->
Relativization bounds the quantifiers by a constant, and the constant has to be
an element of the model, so a stage must be shown constructible. It is, and
cheaply: the formula "true" defines the whole of a set, so a stage is a definable
subset of itself, hence a member of the operator applied to itself, hence
constructible one stage later. With that, relativization to a stage is
instantiated once and its bounded reading is available for the induction.
<!--zh-->
相对化以一个常元界住诸量词，而该常元必须是模型的元素，故须证阶段可构造。确实可构造，而且很廉价：公式「真」定义出一个集合的全体，故阶段是它自身的可定义子集，因而属于施于自身的那个算子，因而在下一阶段可构造。有了这一条，到某阶段的相对化便可实例化一次，其有界读法随即供归纳取用。
<!--/-->

```agda
LsetS : (β : V ℓ) → IsOrd β → S
LsetS β oβ = Lset β
           , 𝒟ₒ→isL β oβ (Lset β)
               (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

module Cor (β : V ℓ) (oβ : IsOrd β) =
  Correct (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id (LsetS β oβ)
```

<!--en-->
## What a stage owes a formula
<!--zh-->
## 一个阶段欠一条公式什么
<!--/-->

<!--en-->
Walking a formula, the unbounded quantifiers are the nodes that cost something:
each carries a matrix, and the previous chapter's step function for that matrix
has to land in the next rung. Collecting those memberships over the formula's
structure gives the debt a rung owes, and it is a tree of the same shape as the
formula, empty at the atoms and at every node that binds nothing.

A universal quantifier contributes the step for the *negated* matrix, because the
argument for it is by contradiction: to know that everything in the stage
satisfies the matrix is to know that nothing in L refutes it, and the refutation
is what has to be caught inside the stage.

The debt only grows easier as the rung grows, since each entry is a membership
and membership is inherited through an ordinal. That is what lets the merges
below raise the pieces to their join.
<!--zh-->
沿公式走下去，要付代价的节点是无界量词：每个带一个矩阵，而上一章为该矩阵所造的步进函数必须落在下一级里。沿公式的结构把这些隶属关系收集起来，就得到一级所欠的债，而它是与公式同形的一棵树，在原子处、以及在每个不绑定任何东西的节点处为空。

全称量词贡献的是**否定后**矩阵的步进，因为对它的论证是反证：要知道阶段中的一切都满足该矩阵，就是要知道 L 中没有东西反驳它，而须被逮进阶段里的正是那个反驳。

这笔债只会随着级的增大而更易偿付，因为每一项都是一条隶属关系，而隶属关系经序数继承。正是这一点使下面的诸次合并能把各部分抬到它们的并处。
<!--/-->

```agda
Answers : ∀ {n} (φ : Formula S n) (σ : V ℓ) (oσ : IsOrd σ) (τ : V ℓ)
        → Type (ℓ-suc ℓ)
Answers (t ∈̇ u)  σ oσ τ = Unit*
Answers (t ≐ u)  σ oσ τ = Unit*
Answers (φ ∧̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
Answers (φ ∨̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
Answers (φ ⇒̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
Answers (¬̇ φ)    σ oσ τ = Answers φ σ oσ τ
Answers ⊤̇        σ oσ τ = Unit*
Answers ⊥̇        σ oσ τ = Unit*
Answers (∃̇ φ)    σ oσ τ = ⟨ Single.Fstep φ σ oσ ∈ τ ⟩ × Answers φ σ oσ τ
Answers (∀̇ φ)    σ oσ τ = ⟨ Single.Fstep (¬̇ φ) σ oσ ∈ τ ⟩ × Answers φ σ oσ τ
Answers (∀̇∈ t φ) σ oσ τ = Answers φ σ oσ τ
Answers (∃̇∈ t φ) σ oσ τ = Answers φ σ oσ τ

Answers-mono : {τ τ' : V ℓ} → ⟨ τ ∈ τ' ⟩ → IsOrd τ'
             → ∀ {n} (φ : Formula S n) (σ : V ℓ) (oσ : IsOrd σ)
             → Answers φ σ oσ τ → Answers φ σ oσ τ'
Answers-mono h o (t ∈̇ u)  σ oσ _        = tt*
Answers-mono h o (t ≐ u)  σ oσ _        = tt*
Answers-mono h o (φ ∧̇ ψ)  σ oσ (a , b) =
  Answers-mono h o φ σ oσ a , Answers-mono h o ψ σ oσ b
Answers-mono h o (φ ∨̇ ψ)  σ oσ (a , b) =
  Answers-mono h o φ σ oσ a , Answers-mono h o ψ σ oσ b
Answers-mono h o (φ ⇒̇ ψ)  σ oσ (a , b) =
  Answers-mono h o φ σ oσ a , Answers-mono h o ψ σ oσ b
Answers-mono h o (¬̇ φ)    σ oσ a        = Answers-mono h o φ σ oσ a
Answers-mono h o ⊤̇        σ oσ _        = tt*
Answers-mono h o ⊥̇        σ oσ _        = tt*
Answers-mono {τ} h o (∃̇ φ) σ oσ (F , a) =
  o .fst {x = τ} {y = Single.Fstep φ σ oσ} F h , Answers-mono h o φ σ oσ a
Answers-mono {τ} h o (∀̇ φ) σ oσ (F , a) =
  o .fst {x = τ} {y = Single.Fstep (¬̇ φ) σ oσ} F h , Answers-mono h o φ σ oσ a
Answers-mono h o (∀̇∈ t φ) σ oσ a        = Answers-mono h o φ σ oσ a
Answers-mono h o (∃̇∈ t φ) σ oσ a        = Answers-mono h o φ σ oσ a
```

<!--en-->
## The joint step
<!--zh-->
## 联合步进
<!--/-->

<!--en-->
Now the step that pays the debt. Recursion on the formula produces, from a rung,
an ordinal above it carrying the whole tree of memberships. Three shapes cover
every constructor: a node that owes nothing takes the rung's own bound; a node
with two children merges its children's ordinals; a quantifier adds one step
function to its child's.

Each shape is written once, over an arbitrary payload with an arbitrary way of
raising it, so the recursion itself is twelve one-line clauses and the ordinal
bookkeeping is not restated at each. The alternative, which is what one writes
first, is three parallel recursions of twelve clauses each computing the ordinal,
its ordinality, and the rung's membership in it; they all traverse the same tree
and project the same bounds.
<!--zh-->
接下来是偿债的那一步。沿公式递归，从一级出发造出它上方的一个序数，带着整棵隶属树。三种形状覆盖了全部构造子：不欠债的节点取该级自己的上界；有两个子节点的合并两个子序数；量词则在子节点之上再添一个步进函数。

每种形状只写一次，针对任意的负载与任意的抬升方式，于是递归本身是十二条一行的子句，而序数的记账不必在每条里重述一遍。另一条路，也是人们最先写出的那条，是三套并行的、各十二条子句的递归，分别算那个序数、它的序数性、以及该级属于它；三者遍历同一棵树，投影同一批上界。
<!--/-->

```agda
private
  Box : (σ : V ℓ) (P : V ℓ → Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
  Box σ P = Σ[ τ ∈ V ℓ ] (IsOrd τ × ⟨ σ ∈ τ ⟩ × P τ)

  Raise : (P : V ℓ → Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
  Raise P = {τ τ' : V ℓ} → ⟨ τ ∈ τ' ⟩ → IsOrd τ' → P τ → P τ'

  unitBox : (σ : V ℓ) (oσ : IsOrd σ) → Box σ (λ _ → Unit*)
  unitBox σ oσ = b .fst , (b .snd .fst , (b .snd .snd .fst , tt*))
    where b = bound2 σ σ oσ oσ

  joinBox : {σ : V ℓ} {P Q : V ℓ → Type (ℓ-suc ℓ)} → Raise P → Raise Q
          → Box σ P → Box σ Q → Box σ (λ τ → P τ × Q τ)
  joinBox {σ} rP rQ (τ₁ , (o₁ , (s₁ , p))) (τ₂ , (o₂ , (_ , q))) =
    b .fst
    , ( ob
      , ( ob .fst {x = τ₁} {y = σ} s₁ (b .snd .snd .fst)
        , ( rP (b .snd .snd .fst) ob p , rQ (b .snd .snd .snd) ob q ) ) )
    where
    b  = bound2 τ₁ τ₂ o₁ o₂
    ob = b .snd .fst

  addBox : {σ : V ℓ} {P : V ℓ → Type (ℓ-suc ℓ)} → Raise P
         → (F : V ℓ) → IsOrd F → Box σ P → Box σ (λ τ → ⟨ F ∈ τ ⟩ × P τ)
  addBox {σ} rP F oF (τ , (oτ , (s , p))) =
    b .fst
    , ( ob
      , ( ob .fst {x = τ} {y = σ} s (b .snd .snd .snd)
        , ( b .snd .snd .fst , rP (b .snd .snd .snd) ob p ) ) )
    where
    b  = bound2 F τ oF oτ
    ob = b .snd .fst

  raiseAns : ∀ {n} (φ : Formula S n) (σ : V ℓ) (oσ : IsOrd σ)
           → Raise (Answers φ σ oσ)
  raiseAns φ σ oσ h o = Answers-mono h o φ σ oσ

gstep : ∀ {n} (φ : Formula S n) (σ : V ℓ) (oσ : IsOrd σ) → Box σ (Answers φ σ oσ)
gstep (t ∈̇ u)  σ oσ = unitBox σ oσ
gstep (t ≐ u)  σ oσ = unitBox σ oσ
gstep (φ ∧̇ ψ)  σ oσ = joinBox (raiseAns φ σ oσ) (raiseAns ψ σ oσ)
                        (gstep φ σ oσ) (gstep ψ σ oσ)
gstep (φ ∨̇ ψ)  σ oσ = joinBox (raiseAns φ σ oσ) (raiseAns ψ σ oσ)
                        (gstep φ σ oσ) (gstep ψ σ oσ)
gstep (φ ⇒̇ ψ)  σ oσ = joinBox (raiseAns φ σ oσ) (raiseAns ψ σ oσ)
                        (gstep φ σ oσ) (gstep ψ σ oσ)
gstep (¬̇ φ)    σ oσ = gstep φ σ oσ
gstep ⊤̇        σ oσ = unitBox σ oσ
gstep ⊥̇        σ oσ = unitBox σ oσ
gstep (∃̇ φ)    σ oσ = addBox (raiseAns φ σ oσ)
                        (Single.Fstep φ σ oσ) (Single.Fstep-ord φ σ oσ)
                        (gstep φ σ oσ)
gstep (∀̇ φ)    σ oσ = addBox (raiseAns φ σ oσ)
                        (Single.Fstep (¬̇ φ) σ oσ) (Single.Fstep-ord (¬̇ φ) σ oσ)
                        (gstep φ σ oσ)
gstep (∀̇∈ t φ) σ oσ = gstep φ σ oσ
gstep (∃̇∈ t φ) σ oσ = gstep φ σ oσ
```

<!--en-->
## The joint ladder
<!--zh-->
## 联合梯
<!--/-->

<!--en-->
Fix a formula and an ordinal holding whatever else the caller needs held: its
constants, and any set it will run the reflection on. One rung's step is the
joint step with that ordinal merged in; iterating from the empty ordinal gives an
ascending chain, so a ladder, and the previous chapter's limit machinery applies
to it unchanged.

Two readings come off the step for free, because they were built into it. The
extra ordinal is in the first rung, hence under the limit. And at every rung, the
whole tree of memberships holds against the next rung, which is the answering
hypothesis in the form the induction wants.
<!--zh-->
固定一条公式，以及一个装着调用方所需的其余东西的序数：它的常元，以及它将要在其上跑反射的任何集合。一级的步进就是把那个序数并进去的联合步进；自空序数迭代，得到上升的链，即一架梯，而上一章的极限机器原样适用。

有两条读法从该步进白得，因为它们本就被造了进去。那个额外的序数落在第一级里，因而落在极限之下。而在每一级上，整棵隶属树都对下一级成立，这正是归纳所要的、作答假设的那个形式。
<!--/-->

```agda
module Mk {n : ℕ} (φ₀ : Formula S n) (κ : V ℓ) (oκ : IsOrd κ)
          (bdd : BoundedFo (Below′ κ) φ₀) where

  private
    jstep : (σ : V ℓ) (oσ : IsOrd σ)
          → Box σ (λ τ → ⟨ κ ∈ τ ⟩ × Answers φ₀ σ oσ τ)
    jstep σ oσ = addBox (raiseAns φ₀ σ oσ) κ oκ (gstep φ₀ σ oσ)

  Gₙ : ℕ → V ℓ
  Gₙ-ord : (N : ℕ) → IsOrd (Gₙ N)
  Gₙ zero        = ∅
  Gₙ (suc N)     = jstep (Gₙ N) (Gₙ-ord N) .fst
  Gₙ-ord zero    = ∅-ord
  Gₙ-ord (suc N) = jstep (Gₙ N) (Gₙ-ord N) .snd .fst

  Gₙ-step : (N : ℕ) → ⟨ Gₙ N ∈ Gₙ (suc N) ⟩
  Gₙ-step N = jstep (Gₙ N) (Gₙ-ord N) .snd .snd .fst

  module Lad = Ladder Gₙ Gₙ-ord Gₙ-step

  β : V ℓ
  β = Lad.top

  oβ : IsOrd β
  oβ = Lad.top-ord

  κ∈β : ⟨ κ ∈ β ⟩
  κ∈β = oβ .fst {x = Gₙ 1} {y = κ}
          (jstep ∅ ∅-ord .snd .snd .snd .fst) (Lad.G∈top 1)

  answersAt : (N : ℕ) → Answers φ₀ (Gₙ N) (Gₙ-ord N) (Gₙ (suc N))
  answersAt N = jstep (Gₙ N) (Gₙ-ord N) .snd .snd .snd .snd
```

<!--en-->
Reading the debt back off gives closure. At a rung, the tree says the matrix's
step function is inside the next rung, and the previous chapter says the matrix's
answering stage is inside its step function; ordinal transitivity composes them
into the answering hypothesis, and the ladder's closure follows.

Two small dictionaries and the induction can start: membership in a stage is
inherited downward, since a stage is transitive, and a term's value lies in the
stage, a constant because it was registered and a variable because the
environment lies there.
<!--zh-->
把那笔债读回来就得到闭包。在某一级上，那棵树说该矩阵的步进函数落在下一级里，而上一章说该矩阵的作答阶段落在它的步进函数里；序数传递性把两者复合成那条作答假设，梯的闭包随之而来。

再加两本小字典，归纳便可开始：属于一个阶段是向下继承的，因为阶段传递；而词项的取值落在该阶段里，常元是因为它被登记过，变元是因为环境落在那里。
<!--/-->

```agda
  private
    closureOf : {k : ℕ} (ψ : Formula S (suc k))
              → ((N : ℕ) → ⟨ Single.Fstep ψ (Gₙ N) (Gₙ-ord N) ∈ Gₙ (suc N) ⟩)
              → ClosedFor β ψ
    closureOf ψ lands = Lad.closure ψ
      (λ N ms → Gₙ-ord (suc N) .fst
                  {x = Single.Fstep ψ (Gₙ N) (Gₙ-ord N)}
                  {y = pickStage ψ (LsetEnv (Gₙ N) (Gₙ-ord N) ms)}
                  (Single.pickLand ψ (Gₙ N) (Gₙ-ord N) ms) (lands N))

  open Cor β oβ using ( _⊨ᴬ_; relativize-correct )

  private
    transβ : {x y : V ℓ} → ⟨ x ∈ y ⟩ → ⟨ y ∈ Lset β ⟩ → ⟨ x ∈ Lset β ⟩
    transβ = layer-trans (Lset-layer β)

    lookupInLayer : ∀ {m} (i : Fin m) (γ : S ^ m) → Below β γ
                  → ⟨ fst (lookup i γ) ∈ Lset β ⟩
    lookupInLayer zero    (a ∷ γ) (ha , _)  = ha
    lookupInLayer (suc i) (a ∷ γ) (_  , hγ) = lookupInLayer i γ hγ

    tmInLayer : ∀ {m} (t : Term S m) (γ : S ^ m) → Below β γ
              → BoundedTm (Below′ β) t → ⟨ fst (⟦ t ⟧ γ) ∈ Lset β ⟩
    tmInLayer (con c) γ _  h = h
    tmInLayer (var i) γ bγ _ = lookupInLayer i γ bγ
```

<!--en-->
## The induction
<!--zh-->
## 归纳
<!--/-->

<!--en-->
Atoms and constants are `refl`{.Agda}, since relativization does not touch them;
the connectives are congruence. A bounded quantifier is the first real step: its
witnesses already lie in the bound, the bound lies in the stage, and the stage is
transitive, so the witnesses lie in the stage and the induction hypothesis
applies to the extended environment.

The existential is the previous chapter. Downward, a witness from the stage is a
witness in L, and the hypothesis converts it. Upward is closure: the truth of the
existential in L is, by definition, the satisfiability the closure lemma consumes,
so it hands back a witness already inside the stage, and the hypothesis applies to
that one instead. Note which witness is used: not the one L happened to supply,
but the one closure chose. That is why nothing circular happens, and why the
stage never has to be a fixed point of anything.

The universal is the existential for the negated matrix, argued by contradiction.
If some element of L failed the matrix, that failure is a witness for the negated
matrix, so closure produces one inside the stage; but the hypothesis says
everything in the stage satisfies the matrix, and the two collide. Deciding
whether the element fails is where the excluded middle enters the induction, and
it is the only place.
<!--zh-->
原子与常元是 `refl`{.Agda}，因为相对化不碰它们；联结词是同余。有界量词是头一步实事：它的见证本就落在界里，界落在阶段里，而阶段传递，故见证落在阶段里，归纳假设遂适用于扩展后的环境。

存在量词就是上一章。向下：来自阶段的见证本就是 L 中的见证，归纳假设把它转过去。向上是闭包：存在量词在 L 中为真，按定义就是闭包引理所消费的那种可满足性，于是它交还一个已在阶段之内的见证，而归纳假设改施于这一个。请注意用的是哪个见证：不是 L 恰好给出的那个，而是闭包选出的那个。这正是何以此处并不循环，也正是何以那个阶段永远不必是任何东西的不动点。

全称量词就是否定后矩阵的存在量词，以反证论之。若 L 的某个元素不满足该矩阵，那次失败便是否定后矩阵的一个见证，于是闭包在阶段之内造出一个；然而假设说阶段中的一切都满足该矩阵，两者相撞。判定那个元素是否失败，正是排中律进入本次归纳之处，而且是唯一之处。
<!--/-->

```agda
  reflectFo : ∀ {m} (χ : Formula S m)
            → ((N : ℕ) → Answers χ (Gₙ N) (Gₙ-ord N) (Gₙ (suc N)))
            → BoundedFo (Below′ β) χ
            → (γ : S ^ m) → Below β γ → (γ ⊨ χ) ≡ (γ ⊨ᴬ χ)

  private
    reflect∃ : ∀ {m} (χ : Formula S (suc m)) → ClosedFor β χ
             → ((N : ℕ) → Answers χ (Gₙ N) (Gₙ-ord N) (Gₙ (suc N)))
             → BoundedFo (Below′ β) χ
             → (γ : S ^ m) → Below β γ → (γ ⊨ (∃̇ χ)) ≡ (γ ⊨ᴬ (∃̇ χ))
    reflect∃ χ cl an bd γ bγ = ⇔toPath fwd bwd
      where
      fwd : ⟨ γ ⊨ (∃̇ χ) ⟩ → ⟨ γ ⊨ᴬ (∃̇ χ) ⟩
      fwd ex = PT.map
        (λ { (q , (fq∈ , satq)) →
             q , (fq∈ , subst ⟨_⟩ (reflectFo χ an bd (q ∷ γ) (fq∈ , bγ)) satq) })
        (cl γ bγ ex)
      bwd : ⟨ γ ⊨ᴬ (∃̇ χ) ⟩ → ⟨ γ ⊨ (∃̇ χ) ⟩
      bwd = PT.map
        (λ { (x , (x∈A , satx)) →
             x , subst ⟨_⟩ (sym (reflectFo χ an bd (x ∷ γ) (x∈A , bγ))) satx })

    reflect∀ : ∀ {m} (χ : Formula S (suc m)) → ClosedFor β (¬̇ χ)
             → ((N : ℕ) → Answers χ (Gₙ N) (Gₙ-ord N) (Gₙ (suc N)))
             → BoundedFo (Below′ β) χ
             → (γ : S ^ m) → Below β γ → (γ ⊨ (∀̇ χ)) ≡ (γ ⊨ᴬ (∀̇ χ))
    reflect∀ χ cl an bd γ bγ = ⇔toPath fwd bwd
      where
      fwd : ⟨ γ ⊨ (∀̇ χ) ⟩ → ⟨ γ ⊨ᴬ (∀̇ χ) ⟩
      fwd h x x∈A =
        subst ⟨_⟩ (reflectFo χ an bd (x ∷ γ) (x∈A , bγ)) (h x)
      bwd : ⟨ γ ⊨ᴬ (∀̇ χ) ⟩ → ⟨ γ ⊨ (∀̇ χ) ⟩
      bwd H x = decide (lem ((x ∷ γ) ⊨ χ))
        where
        decide : (⟨ (x ∷ γ) ⊨ χ ⟩ ⊎ (⟨ (x ∷ γ) ⊨ χ ⟩ → Empty.⊥))
               → ⟨ (x ∷ γ) ⊨ χ ⟩
        decide (inl yes) = yes
        decide (inr no)  = PT.rec (snd ((x ∷ γ) ⊨ χ)) collide
          (cl γ bγ ∣ x , no ∣₁)
          where
          collide : Σ[ q ∈ S ] (⟨ fst q ∈ Lset β ⟩ × ⟨ (q ∷ γ) ⊨ (¬̇ χ) ⟩)
                  → ⟨ (x ∷ γ) ⊨ χ ⟩
          collide (q , (fq∈ , refute)) = Empty.rec
            (refute (subst ⟨_⟩ (sym (reflectFo χ an bd (q ∷ γ) (fq∈ , bγ)))
                       (H q fq∈)))

  reflectFo (t ∈̇ u)  an bd γ bγ = refl
  reflectFo (t ≐ u)  an bd γ bγ = refl
  reflectFo (χ ∧̇ ψ)  an bd γ bγ =
    cong₂ _⊓_ (reflectFo χ (λ N → an N .fst) (bd .fst) γ bγ)
              (reflectFo ψ (λ N → an N .snd) (bd .snd) γ bγ)
  reflectFo (χ ∨̇ ψ)  an bd γ bγ =
    cong₂ _⊔_ (reflectFo χ (λ N → an N .fst) (bd .fst) γ bγ)
              (reflectFo ψ (λ N → an N .snd) (bd .snd) γ bγ)
  reflectFo (χ ⇒̇ ψ)  an bd γ bγ =
    cong₂ _⇒_ (reflectFo χ (λ N → an N .fst) (bd .fst) γ bγ)
              (reflectFo ψ (λ N → an N .snd) (bd .snd) γ bγ)
  reflectFo (¬̇ χ)    an bd γ bγ = cong ¬_ (reflectFo χ an bd γ bγ)
  reflectFo ⊤̇        an bd γ bγ = refl
  reflectFo ⊥̇        an bd γ bγ = refl
  reflectFo (∃̇ χ)    an bd γ bγ =
    reflect∃ χ (closureOf χ (λ N → an N .fst)) (λ N → an N .snd) bd γ bγ
  reflectFo (∀̇ χ)    an bd γ bγ =
    reflect∀ χ (closureOf (¬̇ χ) (λ N → an N .fst)) (λ N → an N .snd) bd γ bγ
  reflectFo (∀̇∈ t χ) an bd γ bγ = ⇔toPath fwd bwd
    where
    tInβ : ⟨ fst (⟦ t ⟧ γ) ∈ Lset β ⟩
    tInβ = tmInLayer t γ bγ (bd .fst)
    fwd : ⟨ γ ⊨ (∀̇∈ t χ) ⟩ → ⟨ γ ⊨ᴬ (∀̇∈ t χ) ⟩
    fwd h x x∈t = subst ⟨_⟩
      (reflectFo χ an (bd .snd) (x ∷ γ) (transβ x∈t tInβ , bγ)) (h x x∈t)
    bwd : ⟨ γ ⊨ᴬ (∀̇∈ t χ) ⟩ → ⟨ γ ⊨ (∀̇∈ t χ) ⟩
    bwd h x x∈t = subst ⟨_⟩
      (sym (reflectFo χ an (bd .snd) (x ∷ γ) (transβ x∈t tInβ , bγ))) (h x x∈t)
  reflectFo (∃̇∈ t χ) an bd γ bγ = ⇔toPath fwd bwd
    where
    tInβ : ⟨ fst (⟦ t ⟧ γ) ∈ Lset β ⟩
    tInβ = tmInLayer t γ bγ (bd .fst)
    fwd : ⟨ γ ⊨ (∃̇∈ t χ) ⟩ → ⟨ γ ⊨ᴬ (∃̇∈ t χ) ⟩
    fwd = PT.map (λ { (x , (x∈t , h)) → x , (x∈t , subst ⟨_⟩
      (reflectFo χ an (bd .snd) (x ∷ γ) (transβ x∈t tInβ , bγ)) h) })
    bwd : ⟨ γ ⊨ᴬ (∃̇∈ t χ) ⟩ → ⟨ γ ⊨ (∃̇∈ t χ) ⟩
    bwd = PT.map (λ { (x , (x∈t , h)) → x , (x∈t , subst ⟨_⟩
      (sym (reflectFo χ an (bd .snd) (x ∷ γ) (transβ x∈t tInβ , bγ))) h) })
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

<!--en-->
Composing the induction with the correctness of relativization turns the bounded
reading back into an ordinary satisfaction, of the relativized formula. That is
the usable form: the right-hand side is Δ₀, so a formula of any complexity has
been traded for a bounded one and a named stage.

Packaged, the theorem takes the formula and any ordinal the caller wants inside
the stage, and returns a stage containing it. The extra ordinal is not a
convenience: the certificate is not inherited by larger stages, so a caller
cannot enlarge the stage afterwards to fit the set it is working with. It has to
say up front what must fit, and the joint step carries it.
<!--zh-->
把这次归纳与相对化的正确性复合，就把有界读法变回一次寻常的满足，只不过对象是相对化后的公式。这是能用的形式：右侧是 Δ₀ 的，故任意复杂度的公式已被换成一条有界公式加一个被点名的阶段。

打包之后，定理接受那条公式与调用方想要落在阶段里的任意序数，交还一个包含它的阶段。那个额外的序数并非图个方便：证书不为更大的阶段所继承，故调用方事后无法把阶段扩大以容纳它手上的集合。它必须事先说清什么必须装得下，而联合步进把它带上。
<!--/-->

```agda
  reflectRel : (γ : S ^ n) → Below β γ
             → (γ ⊨ φ₀) ≡ (γ ⊨ relativize (LsetS β oβ) φ₀)
  reflectRel γ bγ =
    reflectFo φ₀ answersAt (liftFoTo κ∈β φ₀ bdd) γ bγ
    ∙ sym (relativize-correct φ₀ γ)

mkReflect : ∀ {n} (φ : Formula S n) (δ : V ℓ) → IsOrd δ
          → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
              (⟨ δ ∈ β ⟩
               × ((γ : S ^ n) → Below β γ
                  → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ)))
mkReflect φ δ oδ = M.β , (M.oβ , (δ∈β , M.reflectRel))
  where
  bdd = mkBoundedFo φ
  b   = bound2 (bdd .fst) δ (bdd .snd .fst) oδ
  module M = Mk φ (b .fst) (b .snd .fst)
                (liftFoTo (b .snd .snd .fst) φ (bdd .snd .snd))
  δ∈β : ⟨ δ ∈ M.β ⟩
  δ∈β = M.oβ .fst {x = b .fst} {y = δ} (b .snd .snd .snd) M.κ∈β
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`mkReflect`{.Agda} produces, for any formula and any ordinal that must fit inside
it, a stage at which the formula agrees with its relativization to that stage.
Since a relativization is Δ₀, this is the bridge from the whole language to the
bounded fragment the separation chapter can already carve with, and it is the
last thing standing between that chapter's Δ₀ instruments and the two model
fields stated for arbitrary formulas.

The classical cost is unchanged: the excluded middle, in the descent, in deciding
satisfiability, and once more in the universal case here. No choice, and no
well-ordering of L.
<!--zh-->
`mkReflect`{.Agda} 对任意公式、以及任意必须装进去的序数，造出一个阶段，公式在其上与它到该阶段的相对化一致。相对化既是 Δ₀ 的，这便是从整个语言通往有界片段的桥，而分离那一章已能用有界片段来雕；它也是横在那一章的 Δ₀ 器械与两条以任意公式陈述的模型字段之间的最后一物。

经典的代价一如既往：排中律，用在下降处、判定可满足性处，以及此处全称情形再一次。没有选择，也没有 L 的良序。
<!--/-->
