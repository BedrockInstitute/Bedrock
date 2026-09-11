<!--en-->
# Reflection for an arbitrary formula

Reflection for a whole formula must answer the existential subformulas that appear throughout its syntax. A joint closure condition and ordinal ladder are built recursively over the formula, yielding a stage in which the formula has the same truth value as in the full constructible universe.
<!--zh-->
# 任意公式的反射

对整条公式的反射，必须为其语法中各处出现的存在子公式给出答案。本章沿公式递归构造联合封闭条件与序数梯，得到一层，使该公式在其中与整个可构造宇宙中具有相同真值。
<!--ja-->
# 任意の論理式に対する反映

論理式全体の反映では、その構文に現れるすべての存在部分論理式へ答える必要があります。論理式に沿って共同の閉性条件と順序数の梯子を再帰的に作り、その論理式が構成可能宇宙全体と同じ真理値を持つ段階を得ます。
<!--/-->

<!--en-->
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
证明是结构归纳，它需要该层具备两样东西。在无界量词处，需要上一章的闭包，针对该量词自己的矩阵。在有界量词处，需要那个界落在该层里，好让落在界内的一切也落在其中；那正是分离那一章早已会满足的常元条件。

没有哪个针对单一矩阵的极限能同时覆盖全部矩阵，因为闭包不为更大的层所继承：把层扩大，就有更多环境需要它处理。因此这架梯要联合构造：每一级的步进沿公式的结构进行，把其中每个矩阵的单矩阵步进合并起来，连同包含常元的那一层。于是极限对每个矩阵都给出回答，上一章的论证施于其中每一个即可，无须重做。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.FormulaReflection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

lint-agda: keep (⊤̇ names the defining formula behind `LsetS`)

```agda
open import FOL.Manipulation.ConstantBounding using ( BoundedTm; BoundedFo )
open import FOL.Manipulation.Relativization using ( relativize; module Correct )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( ∅-ord; bound2 )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Separation {ℓ} lem
  using ( Below′; liftFoTo; mkBoundedFo )
open import L.ExistentialReflection {ℓ} lem
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

Relativization bounds the quantifiers by a constant, and the constant has to be
an element of the model, so a stage must be shown constructible. It is, and
the argument is direct: the formula "true" defines the whole of a set, so a stage is a definable
subset of itself, hence a member of the operator applied to itself, hence
constructible one stage later. With that, relativization to a stage is
instantiated once and its bounded reading is available for the induction.
<!--zh-->
## 作为元素的层

相对化以一个常元界住诸量词，而该常元必须是模型的元素，故须证层可构造。确实可构造，而且很直接：公式「真」定义出一个集合的全体，故层是它自身的可定义子集，因而属于施于自身的那个算子，因而在下一层可构造。有了这一条，到某层的相对化便可实例化一次，其有界读法随即供归纳取用。
<!--ja-->
## 段階そのものを要素にする

推移的な段階 `Lset σ`{.Agda} は、その全体を定義する恒真な論理式によって次の定義可能段階に現れます。この事実により、後の閉性構成は段階自身をより大きな段階の要素として保持できます。
<!--/-->

<!--en-->
The certificate is sealed, and only it: the stage as an element of the model is
the pair of the stage with the certificate, and the first component has to keep
reducing, since "lies in the bound" and "lies in the stage" are the same
statement only because it does. The certificate is a different matter. It unfolds
through definability into the smallness machinery, and it sits inside a constant,
so every consumer that mentions the constant in a type would carry that unfolding
along; a chapter that separates with a relativized formula takes minutes rather
than seconds without this one line.
<!--zh-->
被封存的只是那份证书：作为模型元素的层是「层与证书」的对，而第一分量必须继续规约，因为「落在界内」与「落在层内」是同一句话，规约恰恰依赖这一点。证书则是另一回事。它经可定义性一路展开到涉及小性的检查，而它又存放于一个常元之中，于是类型中每个提到该常元的部分都会连带承担那次展开的代价；一章若用相对化公式作分离，没有这一行就要以分钟而非秒计。
<!--/-->

```agda
module Cor (β : V ℓ) (oβ : IsOrd β) =
  Correct (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id (LsetS β oβ)
```

<!--en-->
## What a stage owes a formula

Walking a formula, the unbounded quantifiers are the nodes that require extra work:
each carries a matrix, and the previous chapter's step function for that matrix
has to land in the next rung. Collecting those memberships over the formula's
structure gives the conditions a rung must satisfy; it is a tree of the same shape as the
formula, empty at the atoms and at every node that binds nothing.
<!--zh-->
## 层对公式的义务

沿公式走下去，需要额外处理的节点是无界量词：每个带一个矩阵，而上一章为该矩阵所造的步进函数必须落在下一级里。沿公式的结构把这些隶属关系收集起来，便得到该级必须满足的一组条件；它是一棵与公式同形的树，在原子处，以及在每个不绑定任何东西的节点处为空。
<!--ja-->
## 段階が論理式に対して満たす条件

`Answers φ σ τ`{.Agda} は、`σ` から取った環境の下で `φ` の存在部分論理式が真なら、`τ` が対応する証人を含むことを構文に沿って記録します。この条件は `τ` を大きくすると保存されます。
<!--/-->

<!--en-->
A universal quantifier contributes the step for the *negated* matrix, because the
argument for it is by contradiction: to know that everything in the stage
satisfies the matrix is to know that nothing in L refutes it, and the refutation
is what has to be included in the stage.

These conditions only grow easier to satisfy as the rung grows, since each entry
is a membership and membership is inherited through an ordinal. That is what
lets the merges below raise the pieces to their join.
<!--zh-->
全称量词贡献的是**否定后**矩阵的步进，因为对它的论证是反证：要知道层中的一切都满足该矩阵，就是要知道 L 中没有东西反驳它，而须被纳入层里的正是那个反驳。

这些条件只会随着级的增大而更易满足，因为每一项都是一条隶属关系，而隶属关系经序数继承。正是这一点使下面的诸次合并能把各部分提升到它们的并处。
<!--/-->

```agda
Answers : ∀ {n} (φ : Formula S n) (σ : V ℓ) (oσ : IsOrd σ) (τ : V ℓ)
        → Type (ℓ-suc ℓ)
Answers (t ∈̇ u)  σ oσ τ = Unit*
Answers (t ≐ u)  σ oσ τ = Unit*
Answers (φ ∧̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
Answers (φ ∨̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
Answers (φ ⇒̇ ψ)  σ oσ τ = Answers φ σ oσ τ × Answers ψ σ oσ τ
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

Now we construct the step that satisfies these conditions. Recursion on the formula
produces, from a rung, an ordinal above it carrying the whole tree of memberships.
Three shapes cover every constructor: a node with no extra conditions takes the
rung's own bound; a node with two children merges its children's ordinals; a
quantifier adds one step function to its child's.
<!--zh-->
## 联合步骤

接下来构造满足这些条件的一步。沿公式递归，从当前一级出发构造位于其上的一个序数，并携带整棵隶属关系树。三种形状覆盖所有构造子：没有额外条件的节点取当前级自身的上界；有两个子节点时合并两个子序数；量词节点则在子节点之上再加入一个步进函数。
<!--ja-->
## 共同の一段階

論理式の各構成子について、その部分論理式が要求する解答段階を一つの順序数上界へまとめます。存在量化子では母式への一段階の反映も加え、論理式全体の要求を同時に満たします。
<!--/-->

<!--en-->
Each shape is written once, over an arbitrary payload with an arbitrary way of
raising it, so the recursion itself is ten one-line clauses and the ordinal
bookkeeping is not restated at each. The alternative, which is what one writes
first, is three parallel recursions of ten clauses each computing the ordinal,
its ordinality, and the rung's membership in it; they all traverse the same tree
and project the same bounds.
<!--zh-->
每种形状只写一次，并对任意负载与任意提升方式适用，因此递归本身由十条各占一行的子句组成，不必在每条子句中重复序数的计算。另一种直接写法是三套并行递归，每套都有十条子句，分别计算该序数、它的序数性以及当前级属于它；三者遍历同一棵树，并投影同一批上界。
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

Fix a formula and an ordinal holding whatever else the caller needs held: its
constants, and any set it will run the reflection on. One rung's step is the
joint step with that ordinal merged in; iterating from the empty ordinal gives an
ascending chain, so a ladder, and the previous chapter's limit machinery applies
to it unchanged.
<!--zh-->
## 联合梯

固定一条公式，以及一个装着调用方所需的其余东西的序数：它的常元，以及它将要在其上跑反射的任何集合。一级的步进就是把那个序数并进去的联合步进；自空序数迭代，得到上升的链，即一架梯，而上一章的极限机器原样适用。
<!--ja-->
## 共同の梯子

共同の一段階を自然数回反復し、その極限を取ります。有限段階ごとの解答条件が単調性によって極限へ移るため、極限段階は論理式のすべての部分に対して閉じます。
<!--/-->

<!--en-->
Two readings come off the step for free, because they were built into it. The
extra ordinal is in the first rung, hence under the limit. And at every rung, the
whole tree of memberships holds against the next rung, which is the answering
hypothesis in the form the induction wants.
<!--zh-->
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
Reading these conditions back off gives closure. At a rung, the tree gives that the matrix's
step function lies inside the next rung, and the previous chapter gives that the matrix's
answering stage is inside its step function; ordinal transitivity composes them
into the answering hypothesis, and the ladder's closure follows.

Two auxiliary facts let the induction start: membership in a stage is
inherited downward, since a stage is transitive, and a term's value lies in the
stage, a constant because it was registered and a variable because the
environment lies there.
<!--zh-->
把这组条件读回来就得到闭包。在某一级上，那棵树给出该矩阵的步进函数落在下一级里，而上一章给出该矩阵的作答层落在它的步进函数里；序数传递性把两者复合成那条作答假设，梯的闭包随之而来。

再补充两个辅助事实，归纳便可开始：属于一层是向下继承的，因为层传递；而词项的取值落在该层里，常元是因为它被登记过，变元是因为环境落在那里。
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

Atoms and constants are `refl`{.Agda}, since relativization does not touch them;
the connectives are congruence. A bounded quantifier is the first real step: its
witnesses already lie in the bound, the bound lies in the stage, and the stage is
transitive, so the witnesses lie in the stage and the induction hypothesis
applies to the extended environment.
<!--zh-->
## 归纳

原子与常元是 `refl`{.Agda}，因为相对化不碰它们；联结词是同余。有界量词是第一个实质情形：它的见证本就落在界里，界落在层里，而层传递，故见证落在层里，归纳假设遂适用于扩展后的环境。
<!--ja-->
## 帰納法

論理式の構造帰納法により、閉じた段階での充足関係を `L` 全体での充足関係と比較します。原子と結合子は直接従い、量化子では解答条件が必要な証人を段階内へ反映します。
<!--/-->

<!--en-->
The existential case is the one from the previous chapter. Downward, a witness from the stage is a
witness in L, and the hypothesis transfers it. Upward is the case of closure: the truth of the
existential in L is, by definition, the satisfiability the closure lemma consumes,
so closure returns a witness already inside the stage, and the hypothesis applies to
that one instead. Note which witness is used: not the one L happened to supply,
but the one closure chose. That is why no circularity arises here, and why the
stage never has to be a fixed point of anything.

The universal case is the existential case for the negated matrix, argued by contradiction.
If some element of L failed the matrix, that failure would be a witness for the negated
matrix, so closure would produce one inside the stage; but the hypothesis asserts that
everything in the stage satisfies the matrix, a contradiction. Deciding
whether the element fails is where the excluded middle enters the induction, and
it is the only place.
<!--zh-->
存在量词的情形归结为上一章的论证。向下：来自层的见证本来就是 L 中的见证，归纳假设把它转移过去。向上是闭包的情形：存在量词在 L 中为真，按定义正是闭包引理所处理的那种可满足性，于是闭包返回一个已在层之内的见证，归纳假设转而适用于这一个见证。请注意用的是哪个见证：不是 L 恰好给出的那个，而是闭包选出的那个。这正是此处不产生循环的原因，也正是那一层永远不必成为任何东西的不动点的原因。

全称量词的情形就是否定后矩阵的存在量词的情形，用反证法论证。若 L 的某个元素不满足该矩阵，那次失败便是否定后矩阵的一个见证，于是闭包会在层之内造出一个这样的见证；然而归纳假设断言层中的一切都满足该矩阵，两者矛盾。判定那个元素是否失败，正是排中律进入本次归纳之处，而且是唯一之处。
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
          (cl γ bγ ∣ x , (λ yes → lift (no yes)) ∣₁)
          where
          collide : Σ[ q ∈ S ] (⟨ fst q ∈ Lset β ⟩ × ⟨ (q ∷ γ) ⊨ (¬̇ χ) ⟩)
                  → ⟨ (x ∷ γ) ⊨ χ ⟩
          collide (q , (fq∈ , refute)) = Empty.rec
            (lower (refute (subst ⟨_⟩
              (sym (reflectFo χ an bd (q ∷ γ) (fq∈ , bγ))) (H q fq∈))))

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

Composing the induction with the correctness of relativization turns the bounded
reading back into an ordinary satisfaction, of the relativized formula. That is
the convenient form to use: the right-hand side is Δ₀, so a formula of any complexity has
been replaced by a bounded one and a named stage.
<!--zh-->
## 反射定理

把这次归纳与相对化的正确性复合，就把有界读法变回一次寻常的满足，只不过对象是相对化后的公式。这是便于使用的形式：右侧是 Δ₀ 的，故任意复杂度的公式已被换成一条有界公式加一个被明确指出的层。
<!--ja-->
## 反映定理

任意の論理式、出発段階、そこから取った環境に対し、より大きな順序数段階を構成します。その段階は論理式について閉じ、制限構造での真理値が `L` 全体での真理値と一致します。
<!--/-->

<!--en-->
Packaged, the theorem takes the formula and any ordinal the caller wants inside
the stage, and returns a stage containing it. The extra ordinal is not a
convenience: the certificate is not inherited by larger stages, so a caller
cannot enlarge the stage afterwards to fit the set it is working with. It has to
say up front what must fit, and the joint step carries it.

The package is sealed, and this is the seal that matters most in the book so far.
Transparent, the stage it names unfolds through the joint step, the bounding
lemma and the excluded middle at every rung; a consumer that mentions the stage
in a type, as both consumers do, would drag that whole unfolding into every
conversion check, and the next chapter simply does not finish. Sealed, the stage
is a name, and the four things a consumer needs of it are the four the package
already states.
<!--zh-->
整理成定理后，它接受一条公式和调用方要求包含在层中的任意序数，并返回一个包含该序数的层。这个额外序数不可省略：证书不会由较大层继承，所以调用方不能事后扩大层，以容纳自己已有的集合。调用方必须预先说明需要包含什么，联合步进会把这一要求一同带入构造。

这个包被封装起来，而这是本书至此最要紧的一次封装。若是透明的，它所命名的层会在每一级上一路展开到联合步进、界层引理与排中律；而凡在类型中提到该层的使用者，都会把那整次展开带进每一次转换检查，两个使用者恰恰都在类型中提到它，于是下一章根本无法完成。封装之后，那一层只是一个名字，使用者向它索取的四样东西，正是这个包已经陈述的四样。
<!--/-->

```agda
  reflectRel : (γ : S ^ n) → Below β γ
             → (γ ⊨ φ₀) ≡ (γ ⊨ relativize (LsetS β oβ) φ₀)
  reflectRel γ bγ =
    reflectFo φ₀ answersAt (liftFoTo κ∈β φ₀ bdd) γ bγ
    ∙ sym (relativize-correct φ₀ γ)

opaque
  mkReflect : ∀ {n} (φ : Formula S n) (δ : V ℓ) → IsOrd δ
            → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
                (⟨ δ ∈ β ⟩
                 × ((γ : S ^ n) → Below β γ
                    → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ)))
  mkReflect φ δ oδ = M.β , (M.oβ , (δ∈β , M.reflectRel))
    where
    bdd : Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)
    bdd = mkBoundedFo φ
    b : Σ[ τ ∈ V ℓ ] (IsOrd τ × ⟨ bdd .fst ∈ τ ⟩ × ⟨ δ ∈ τ ⟩)
    b = bound2 (bdd .fst) δ (bdd .snd .fst) oδ
    module M = Mk φ (b .fst) (b .snd .fst)
                  (liftFoTo (b .snd .snd .fst) φ (bdd .snd .snd))
    δ∈β : ⟨ δ ∈ M.β ⟩
    δ∈β = M.oβ .fst {x = b .fst} {y = δ} (b .snd .snd .snd) M.κ∈β
```

<!--en-->
## Recap

`mkReflect`{.Agda} produces, for any formula and any ordinal that must fit inside
it, a stage at which the formula agrees with its relativization to that stage.
Since a relativization is Δ₀, this is the route from the whole language to the
bounded fragment that the separation chapter can already use to carve out sets, and it is the final
link between that chapter's Δ₀ instruments and the two model fields stated for
arbitrary formulas.
<!--zh-->
## 小结

`mkReflect`{.Agda} 对任意公式以及任意必须装进去的序数，造出一层，公式在其上与它到该层的相对化一致。相对化是 Δ₀ 的，这便是从整个语言通向有界片段的途径：分离那一章因此能用有界片段来表述；它也是那一章的 Δ₀ 工具与两条以任意公式陈述的模型字段之间的最后一环。
<!--ja-->
## まとめ

論理式の全存在部分式に対する解答条件を一つの梯子へ統合すると、任意の有限な論理式を反映する段階が得られます。主定理はこの段階での評価と `L` 全体での評価を同定します。
<!--/-->

<!--en-->
The classical cost is unchanged: the excluded middle, in the descent, in deciding
satisfiability, and once more in the universal case here. No choice, and no
well-ordering of L.
<!--zh-->
经典的代价一如既往：排中律，用在下降处、判定可满足性处，以及此处全称情形再用一次。这里没有用到选择，也没有用到 L 的良序。
<!--/-->
