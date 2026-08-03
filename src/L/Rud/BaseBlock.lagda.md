# The base block: hereditary finiteness at Sset ω

<!--en-->
The bridge's reduction asks for one Def stage to stay inside the rud tower, and
DefInJ left the missing piece standing as a fragment: a member of a limit level
whose definable power is again a member. At the first limit this chapter closes
the case outright. The statement is the `γ = ω` instance of the fragment
discharge: for `ζ ∈ ω`, `Lset (sucV ζ) ∈ Sset ω` follows from
`Lset ζ ∈ Sset ω`. Since a successor stage is the definable power of the stage
below it, this is a claim about a member of `Sset ω`: its definable power is
again a member.

Nothing about the rud closure is spent here, and nothing can be: no member of
`Sset ω` is closed under the sixteen operations, because every member of every
finite stage is finite and `Sset ω` is their union. What is spent is hereditary
finiteness in the exact sense the L-side twin chapter established: a tally, a
finite family that hits every member. A member `C` of `Sset ω` enters at a
finite stage, so it is finite; its definable subsets are then all of its
subsets, each one a finite set of members of `C`, hence a finite set of members
of `Sset ω`, hence a member of `Sset ω`; and the collection of them is finite,
hence again a member. Three small engine pieces carry this: the limit
predicate at `ω`, the S-side tally of every finite stage, and the lemma that a
finite set of members of `Sset ω` is a member of `Sset ω`.
<!--zh-->
桥的归约要求一个 Def 阶段保持在初步函数塔内，而 DefInJ 把缺件作为片段留在原地：某极限层的一个成员，其可定义幂仍是成员。在第一个极限处，本章把这情形整个关闭。陈述是片段兑付的 `γ = ω` 实例：对 `ζ ∈ ω`，由 `Lset ζ ∈ Sset ω` 推出 `Lset (sucV ζ) ∈ Sset ω`。由于后继阶段是其下阶段的可定义幂，这就是关于 `Sset ω` 一个成员的断言：它的可定义幂仍是成员。

此处不花费初步闭包的任何东西，也无从花费：`Sset ω` 的任何成员都不对十六个运算封闭，因为每个有穷阶段的每个成员都有穷，而 `Sset ω` 是它们的并。花费的是遗传有穷性，取 L 侧孪生章确立的精确含义：一份点名册，即一个命中每个成员的有穷族。`Sset ω` 的成员 `C` 在有穷阶段进场，故有穷；它的可定义子集于是就是它的全部子集，每一份都是 `C` 的成员所成的有穷集合，从而是 `Sset ω` 的成员所成的有穷集合，进而是 `Sset ω` 的成员；而它们所成的那个集合有穷，故仍是成员。三件小型引擎件承载这一切：`ω` 处的极限谓词、每个有穷阶段的 S 侧点名册，以及「`Sset ω` 的成员所成的有穷集合是 `Sset ω` 的成员」这条引理。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.BaseBlock {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; ∈∈ₛ; _≡ₕ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
module IS = InfinitySet {ℓ}
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( _+_; _·_ )
open import Cubical.Data.Bool using ( Bool )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Equiv using ( _≃_; invEq; retEq )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; Lset-suc )
open import L.Ordinal {ℓ} using ( numeral-ord; ω-ord; #∈ω )
open import L.Choice.Finite {ℓ} lem
  using ( Tally; StageOrder; module PowerStep; stageOrder; maskCount; maskAt; mask-onto )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec )
open import L.Rud.Step {ℓ} lem A using
  ( step; Sset; Sset-in; Sset-out; Sset-suc; Sset-trans; step-in; step-in-self; step-∈
  ; step-in-img; step-out; StepArm; arm-member; arm-self; arm-image
  ; u'; u'-in; u-self-in; u'-cases; split→u'
  ; Op16; Fof; Fof-f0; Fof-f5; f0; f5
  ; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12; op13; op14; op15
  ; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isSucc; predecessor-mem )
open import Cubical.Data.FinData.Properties
  using ( module FinSumChar; module FinProdChar )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The first limit
<!--zh-->
## 第一个极限
<!--/-->

<!--en-->
The tower's limit machinery (the limit equation, the successor-closure fact,
the rud closure of the level) is parameterized by the limit predicate, and at
`ω` two of its three conjuncts are missing from the record: that `ω` is not
zero, and that it is not a successor. The first is the numeral zero entering
`ω`. The second takes a hypothetical predecessor: the predecessor belongs to
`ω`, so it is one of the numerals, so its successor is also a numeral and hence
a member of `ω`; but its successor is `ω` itself, and regularity forbids
self-membership. Both directions of the numeral characterization are read off
the delivered ordinal chapter's membership facts.
<!--zh-->
塔的极限机器 (极限方程、后继封闭事实、层的初步封闭) 都以极限谓词为参数，而在 `ω` 处，它的三个合取项中两个缺于记录：`ω` 非零，且 `ω` 非后继。其一是数码零进入 `ω`。其二取一个假想的前驱：前驱属于 `ω`，故它是某个数码，于是它的后继也是数码，从而是 `ω` 的成员；但它的后继就是 `ω` 自身，正则性禁止自属。数码刻画的两个方向都从已交付的序数章的成员事实读出。
<!--/-->

```agda
limω : ⟨ isLimit IS.ω ⟩
limω = (ω-ord , (ω-not-zero , ω-not-succ))
  where
  ω-not-zero : (IS.ω ≡ ∅) → Empty.⊥
  ω-not-zero eq = ∅-empty ∅ (∈∈ₛ {a = ∅} {b = ∅} .fst (subst (λ w → ⟨ ∅ ∈ˢ w ⟩) eq (#∈ω zero)))
  ω-not-succ : ⟨ isSucc IS.ω ⟩ → Empty.⊥
  ω-not-succ (β , ordβ , eq) = PT.rec Empty.isProp⊥ numeral-of (predecessor-mem β IS.ω eq)
    where
    numeral-of : Σ[ k ∈ Lift ℕ ] (IS.# (lower k) ≡ β) → Empty.⊥
    numeral-of (k , q) = ∈-irrefl IS.ω
      (subst (λ w → ⟨ w ∈ˢ IS.ω ⟩) (cong IS.sucV q ∙ eq) (#∈ω (suc (lower k))))
```

<!--en-->
## Tallies on the S-tower
<!--zh-->
## S 塔上的点名册
<!--/-->

<!--en-->
Finiteness keeps the form the L-side twin established: a `Tally`, a family
indexed by a finite type that hits every member, with no injectivity asked for.
The new content is the S-tower's own tally: every `Sset (# n)` is finite. The
step is a union over the finite square, so a tally of `u` yields one of
`step u` in three pieces: a tally of `u ∪ {u}` (the members of `u` plus `u`
itself), an enumeration of the argument square as an index arithmetic on
`Fin`, and the sixteen image values over that square, read through the sealed
membership surface of the step. The square is enumerated at the finite index
by the library's sum and product equivalences, and memberships are read at
small indices only, which is the recorded discipline for this chapter's wall
class: no fiber is ever extracted from the presentation of a union.
<!--zh-->
有穷性保持 L 侧孪生章确立的形式：一份 `Tally`，即以有穷类型为索引、命中每个成员的族，不要求单射。新内容是 S 塔自己的点名册：每个 `Sset (# n)` 都有穷。step 是有限平方上的并，故 `u` 的点名册给出 `step u` 的，分三件：`u ∪ {u}` 的点名册 (`u` 的成员加 `u` 自身)、作为 `Fin` 索引算术的参数平方枚举，以及该平方上十六个像值，全部经由 step 的封印成员表面读出。平方在有穷索引处由库的和与积等价枚举，成员关系只在小区处读出，这正是本章墙类的既定纪律：绝不从某个并的表示中提取纤维。
<!--/-->

```agda
-- perf: R-35/P-c: the square and the sixteen images are enumerated at the Fin
-- index (FinSumChar/FinProdChar); membership is read only through the sealed
-- step surface and the sett's small index, never via ⋃-fiber extraction
module Sside (u : S) (t : Tally u) where
  open Tally t public

  K : ℕ
  K = suc size

  up : Fin K → S
  up zero    = u
  up (suc i) = item i

  up-inside : (i : Fin K) → ⟨ up i ∈ˢ u' u ⟩
  up-inside zero    = u-self-in u
  up-inside (suc i) = u'-in u (item i) (inside i)

  up-onto : (x : S) → ⟨ x ∈ˢ u' u ⟩ → ∥ Σ[ i ∈ Fin K ] (up i ≡ x) ∥₁
  up-onto x h = go (u'-cases u x h)
    where
    go : (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ∥ Σ[ i ∈ Fin K ] (up i ≡ x) ∥₁
    go (inl x∈u) = PT.map (λ { (i , q) → suc i , q }) (onto x x∈u)
    go (inr x≡u) = ∣ zero , sym x≡u ∣₁

  name : Fin K → ⟪ u' u ⟫
  name i = ∈-asFiber {a = up i} {b = u' u} (up-inside i) .fst

  name-eq : (i : Fin K) → ⟪ u' u ⟫↪ (name i) ≡ up i
  name-eq i = ∈-asFiber {a = up i} {b = u' u} (up-inside i) .snd

  Esq : Fin K × Fin K ≃ Fin (K · K)
  Esq = FinProdChar.Equiv K K

  pairIdx : Fin K → Fin K → Fin (K · K)
  pairIdx i j = Esq .fst (i , j)

  pair-ret : (i j : Fin K) → invEq Esq (pairIdx i j) ≡ (i , j)
  pair-ret i j = retEq Esq (i , j)

  imgItem : (i : Op16) → Fin (K · K) → S
  imgItem i j = Fof i (⟪ u' u ⟫↪ (name (invEq Esq j .fst)))
                      (⟪ u' u ⟫↪ (name (invEq Esq j .snd)))

  img-inside : (i : Op16) (j : Fin (K · K)) → ⟨ imgItem i j ∈ˢ step u ⟩
  img-inside i j = step-in-img u (imgItem i j) i a b a∈ b∈ refl
    where
    p : Fin K × Fin K
    p = invEq Esq j
    a : S
    a = ⟪ u' u ⟫↪ (name (p .fst))
    b : S
    b = ⟪ u' u ⟫↪ (name (p .snd))
    a∈ : ⟨ a ∈ˢ u' u ⟩
    a∈ = ∈∈ₛ {a = a} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (name (p .fst)))
    b∈ : ⟨ b ∈ˢ u' u ⟩
    b∈ = ∈∈ₛ {a = b} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (name (p .snd)))

  img-onto : (i : Op16) (a b : S) (a∈ : ⟨ a ∈ˢ u' u ⟩) (b∈ : ⟨ b ∈ˢ u' u ⟩)
           → (x : S) → ⟨ x ≡ₕ Fof i a b ⟩
           → ∥ Σ[ j ∈ Fin (K · K) ] (imgItem i j ≡ x) ∥₁
  img-onto i a b a∈ b∈ x x≡ =
    PT.rec squash₁ (λ { (ia , ea) →
      PT.map (λ { (ib , eb) → pairIdx ia ib , path ia ib ea eb }) (up-onto b b∈) })
      (up-onto a a∈)
    where
    path : (ia ib : Fin K) → up ia ≡ a → up ib ≡ b → imgItem i (pairIdx ia ib) ≡ x
    path ia ib ea eb =
      cong₂ (Fof i) (first ia ea) (second ib eb) ∙ sym x≡
      where
      first : (ia : Fin K) → up ia ≡ a
            → ⟪ u' u ⟫↪ (name (invEq Esq (pairIdx ia ib) .fst)) ≡ a
      first ia ea = cong (λ q → ⟪ u' u ⟫↪ (name (q .fst))) (pair-ret ia ib) ∙ name-eq ia ∙ ea
      second : (ib : Fin K) → up ib ≡ b
             → ⟪ u' u ⟫↪ (name (invEq Esq (pairIdx ia ib) .snd)) ≡ b
      second ib eb = cong (λ q → ⟪ u' u ⟫↪ (name (q .snd))) (pair-ret ia ib) ∙ name-eq ib ∙ eb

  sixteen : ℕ
  sixteen = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))

  op16 : Fin sixteen → Op16
  op16 zero                                     = op0
  op16 (suc zero)                               = op1
  op16 (suc (suc zero))                         = op2
  op16 (suc (suc (suc zero)))                   = op3
  op16 (suc (suc (suc (suc zero))))             = op4
  op16 (suc (suc (suc (suc (suc zero)))))       = op5
  op16 (suc (suc (suc (suc (suc (suc zero)))))) = op6
  op16 (suc (suc (suc (suc (suc (suc (suc zero)))))))                     = op7
  op16 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))               = op8
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))         = op9
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))   = op10
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = op11
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = op12
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = op13
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = op14
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = op15

  op16Onto : (i : Op16) → Σ[ j ∈ Fin sixteen ] (op16 j ≡ i)
  op16Onto op0  = zero , refl
  op16Onto op1  = suc zero , refl
  op16Onto op2  = suc (suc zero) , refl
  op16Onto op3  = suc (suc (suc zero)) , refl
  op16Onto op4  = suc (suc (suc (suc zero))) , refl
  op16Onto op5  = suc (suc (suc (suc (suc zero)))) , refl
  op16Onto op6  = suc (suc (suc (suc (suc (suc zero))))) , refl
  op16Onto op7  = suc (suc (suc (suc (suc (suc (suc zero)))))) , refl
  op16Onto op8  = suc (suc (suc (suc (suc (suc (suc (suc zero))))))) , refl
  op16Onto op9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) , refl
  op16Onto op10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) , refl
  op16Onto op11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) , refl
  op16Onto op12 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) , refl
  op16Onto op13 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) , refl
  op16Onto op14 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) , refl
  op16Onto op15 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) , refl

  E16 : Fin sixteen × Fin (K · K) ≃ Fin (sixteen · (K · K))
  E16 = FinProdChar.Equiv sixteen (K · K)

  imgItem16 : Fin (sixteen · (K · K)) → S
  imgItem16 j = imgItem (op16 (invEq E16 j .fst)) (invEq E16 j .snd)

  img-inside16 : (j : Fin (sixteen · (K · K))) → ⟨ imgItem16 j ∈ˢ step u ⟩
  img-inside16 j = img-inside (op16 (invEq E16 j .fst)) (invEq E16 j .snd)

  img-onto16 : (i : Op16) (a b : S) (a∈ : ⟨ a ∈ˢ u' u ⟩) (b∈ : ⟨ b ∈ˢ u' u ⟩)
             → (x : S) → ⟨ x ≡ₕ Fof i a b ⟩
             → ∥ Σ[ j ∈ Fin (sixteen · (K · K)) ] (imgItem16 j ≡ x) ∥₁
  img-onto16 i a b a∈ b∈ x x≡ = PT.map atIdx (img-onto i a b a∈ b∈ x x≡)
    where
    atIdx : Σ[ j ∈ Fin (K · K) ] (imgItem i j ≡ x)
          → Σ[ j ∈ Fin (sixteen · (K · K)) ] (imgItem16 j ≡ x)
    atIdx (j , q) = E16 .fst (op16Onto i .fst , j) , path j q
      where
      path : (j : Fin (K · K)) → imgItem i j ≡ x → imgItem16 (E16 .fst (op16Onto i .fst , j)) ≡ x
      path j q = cong (λ r → imgItem (op16 (r .fst)) (r .snd)) (retEq E16 (op16Onto i .fst , j))
               ∙ cong (λ w → Fof w (⟪ u' u ⟫↪ (name (invEq Esq j .fst)))
                                 (⟪ u' u ⟫↪ (name (invEq Esq j .snd)))) (op16Onto i .snd)
               ∙ q

  Esum : Fin K ⊎ Fin (sixteen · (K · K)) ≃ Fin (K + sixteen · (K · K))
  Esum = FinSumChar.Equiv K (sixteen · (K · K))

  stepSplit : Fin K ⊎ Fin (sixteen · (K · K)) → S
  stepSplit (inl i)  = up i
  stepSplit (inr j') = imgItem16 j'

  stepItem : Fin (K + sixteen · (K · K)) → S
  stepItem j = stepSplit (invEq Esum j)

  step-inside : (j : Fin (K + sixteen · (K · K))) → ⟨ stepItem j ∈ˢ step u ⟩
  step-inside j = go (invEq Esum j)
    where
    go : (s : Fin K ⊎ Fin (sixteen · (K · K))) → ⟨ stepSplit s ∈ˢ step u ⟩
    go (inl zero)    = step-in-self u
    go (inl (suc i)) = step-in u (item i) (inside i)
    go (inr j')      = img-inside16 j'

  step-onto : (x : S) → ⟨ x ∈ˢ step u ⟩
            → ∥ Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x) ∥₁
  step-onto x x∈ = PT.rec squash₁ go (step-out u x x∈)
    where
    atInl : Σ[ i ∈ Fin K ] (up i ≡ x)
          → Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x)
    atInl (i , q) = Esum .fst (inl i) , (cong stepSplit (retEq Esum (inl i)) ∙ q)
    atInr : Σ[ j' ∈ Fin (sixteen · (K · K)) ] (imgItem16 j' ≡ x)
          → Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x)
    atInr (j' , q) = Esum .fst (inr j') , (cong stepSplit (retEq Esum (inr j')) ∙ q)
    go : StepArm u x → ∥ Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x) ∥₁
    go (arm-member x∈u) = PT.map atInl (up-onto x (u'-in u x x∈u))
    go (arm-self x≡u)   = ∣ atInl (zero , sym x≡u) ∣₁
    go (arm-image i a b a-split b-split x≡) =
      PT.map atInr
        (img-onto16 i a b (split→u' u a a-split) (split→u' u b b-split) x x≡)

  stepTally : Tally (step u)
  stepTally = record
    { size   = K + sixteen · (K · K)
    ; item   = stepItem
    ; inside = step-inside
    ; onto   = step-onto }
```

```agda
sTally : (n : ℕ) → Tally (Sset (IS.# n))
sTally zero = record
  { size   = zero
  ; item   = λ ()
  ; inside = λ ()
  ; onto   = λ x x∈ → Empty.rec (sset0-empty x x∈) }
  where
  sset0-empty : (x : S) → ⟨ x ∈ˢ Sset ∅ ⟩ → Empty.⊥
  sset0-empty x x∈ = PT.rec Empty.isProp⊥ step0 (Sset-out ∅ x x∈)
    where
    step0 : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → Empty.⊥
    step0 (δ , δ∈ , _) = ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈)
sTally (suc n) = record
  { size   = Tally.size st
  ; item   = Tally.item st
  ; inside = λ i → subst (λ w → ⟨ Tally.item st i ∈ˢ w ⟩) (sym stepEq)
                        (Tally.inside st i)
  ; onto   = λ x x∈ → Tally.onto st x (subst (λ w → ⟨ x ∈ˢ w ⟩) stepEq x∈) }
  where
  st : Tally (step (Sset (IS.# n)))
  st = Sside.stepTally (Sset (IS.# n)) (sTally n)
  stepEq : Sset (IS.# (suc n)) ≡ step (Sset (IS.# n))
  stepEq = Sset-suc (IS.# n)
```

<!--en-->
## Finite sets of members of the limit level
<!--zh-->
## 极限层成员所成的有穷集合
<!--/-->

<!--en-->
The workhorse lemma: a finite table whose entries all lie in `Sset ω` spans a
set that is itself a member of `Sset ω`. The proof is an induction on the
table's length. The empty table is the empty set, which enters `Sset ω` through
the first numeral. A table with a head is the singleton of its head united with
the tail's set, and the union is realized as the union operation applied to the
unordered pair of the singleton and the tail: both are members of `Sset ω` by
the induction hypothesis, and the limit level is closed under every operation
of the basis (`Jset-rud`), so the composite is a member. The equality between
the table and the operation composite is proved extensionally in both
directions, by the two-armed membership specifications of the pair and the
union. The tally form of the lemma follows: a finite set all of whose members
lie in the limit level is a table of its own tally entries, so the table lemma
applies.
<!--zh-->
工作马引理：一张条目全部落在 `Sset ω` 里的有穷表，张成的集合自身是 `Sset ω` 的成员。证明沿表的长度归纳。空表即空集，空集经第一个数码进入 `Sset ω`。带头的表是头之单点集与尾之集合的并，而这个并实现为并运算作用于单点集与尾集所成的无序对：二者由归纳假设都是 `Sset ω` 的成员，而极限层对基底的每个运算封闭 (`Jset-rud`)，故复合仍是成员。表与运算复合之间的等式按两个方向外延地证明，用对与并的双臂成员规格。点名册形式的引理随之而来：成员全部落在极限层里的有穷集合，就是其点名册条目所成的表，故表引理适用。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

finSet0∅ : (h : Fin 0 → S) → finSet 0 h ≡ ∅
finSet0∅ h = ext-⊆ sub sup
  where
  sub : (y : S) → ⟨ y ∈ˢ finSet 0 h ⟩ → ⟨ y ∈ˢ ∅ ⟩
  sub y y∈ = PT.rec (snd (y ∈ˢ ∅)) (λ { (() , _) }) (finSet-out 0 h y y∈)
  sup : (y : S) → ⟨ y ∈ˢ ∅ ⟩ → ⟨ y ∈ˢ finSet 0 h ⟩
  sup y y∈ = Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))

finSetSuc : (n : ℕ) (h : Fin (suc n) → S)
          → finSet (suc n) h
          ≡ F5 (F0 (F0 (h zero) (h zero)) (finSet n (h ∘ suc))) (h zero)
finSetSuc n h = ext-⊆ sub sup
  where
  X : S
  X = finSet n (h ∘ suc)
  P : S
  P = F0 (F0 (h zero) (h zero)) X
  sub : (y : S) → ⟨ y ∈ˢ finSet (suc n) h ⟩ → ⟨ y ∈ˢ F5 P (h zero) ⟩
  sub y y∈ = PT.rec (snd (y ∈ˢ F5 P (h zero))) go (finSet-out (suc n) h y y∈)
    where
    go : Σ[ i ∈ Fin (suc n) ] (h i ≡ y) → ⟨ y ∈ˢ F5 P (h zero) ⟩
    go (zero , q) = F5-spec P (h zero) y .snd
      ∣ F0 (h zero) (h zero)
      , ( F0-spec (F0 (h zero) (h zero)) X (F0 (h zero) (h zero)) .snd ∣ inl refl ∣₁
        , F0-spec (h zero) (h zero) y .snd ∣ inl (sym q) ∣₁ ) ∣₁
    go (suc i , q) = F5-spec P (h zero) y .snd
      ∣ X , ( F0-spec (F0 (h zero) (h zero)) X X .snd ∣ inr refl ∣₁
            , finSet-in n (h ∘ suc) y ∣ i , q ∣₁ ) ∣₁
  sup : (y : S) → ⟨ y ∈ˢ F5 P (h zero) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
  sup y y∈ = PT.rec (snd (y ∈ˢ finSet (suc n) h)) go
    (F5-spec P (h zero) y .fst y∈)
    where
    go : Σ[ v ∈ S ] ⟨ (v ∈ˢ P) ⊓ (y ∈ˢ v) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
    go (v , v∈P , y∈v) = atV
      (F0-spec (F0 (h zero) (h zero)) X v .fst v∈P)
      where
      atV : ⟨ (v ≡ₕ F0 (h zero) (h zero)) ⊔ (v ≡ₕ X) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
      atV hv = PT.rec (snd (y ∈ˢ finSet (suc n) h)) atCases hv
        where
        atCases : (⟨ v ≡ₕ F0 (h zero) (h zero) ⟩ ⊎ ⟨ v ≡ₕ X ⟩) → ⟨ y ∈ˢ finSet (suc n) h ⟩
        atCases (inl v≡) = atSingl
          (F0-spec (h zero) (h zero) y .fst (subst (λ w → ⟨ y ∈ˢ w ⟩) v≡ y∈v))
          where
          atSingl : ⟨ (y ≡ₕ h zero) ⊔ (y ≡ₕ h zero) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
          atSingl hy = PT.rec (snd (y ∈ˢ finSet (suc n) h)) atEq hy
            where
            atEq : (⟨ y ≡ₕ h zero ⟩ ⊎ ⟨ y ≡ₕ h zero ⟩) → ⟨ y ∈ˢ finSet (suc n) h ⟩
            atEq (inl y≡) = finSet-in (suc n) h y ∣ zero , sym y≡ ∣₁
            atEq (inr y≡) = finSet-in (suc n) h y ∣ zero , sym y≡ ∣₁
        atCases (inr v≡) = atX (subst (λ w → ⟨ y ∈ˢ w ⟩) v≡ y∈v)
          where
          atX : ⟨ y ∈ˢ X ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
          atX y∈X = PT.rec (snd (y ∈ˢ finSet (suc n) h))
            (λ { (i , q) → finSet-in (suc n) h y ∣ suc i , q ∣₁ })
            (finSet-out n (h ∘ suc) y y∈X)

Sset-zero-∅ : Sset ∅ ≡ ∅
Sset-zero-∅ = ext-⊆ sub sup
  where
  sub : (x : S) → ⟨ x ∈ˢ Sset ∅ ⟩ → ⟨ x ∈ˢ ∅ ⟩
  sub x x∈ = PT.rec (snd (x ∈ˢ ∅)) step0 (Sset-out ∅ x x∈)
    where
    step0 : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ ∅ ⟩
    step0 (δ , δ∈ , _) = Empty.rec (∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈))
  sup : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → ⟨ x ∈ˢ Sset ∅ ⟩
  sup x x∈ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈))

∅∈Ssetω : ⟨ ∅ ∈ˢ Sset IS.ω ⟩
∅∈Ssetω = Sset-in IS.ω ∅ ∅ (#∈ω 0)
  (subst (λ w → ⟨ ∅ ∈ˢ step w ⟩) (sym Sset-zero-∅) (step-∈ ∅))

op-in-J : (i : Op16) → (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩
        → ⟨ Fof i a b ∈ˢ Sset IS.ω ⟩
op-in-J i a b a∈ b∈ = Jset-rud IS.ω limω i a b a∈ b∈

opF0 : (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩ → ⟨ F0 a b ∈ˢ Sset IS.ω ⟩
opF0 a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (Fof-f0 a b) (op-in-J f0 a b a∈ b∈)

opF5 : (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩ → ⟨ F5 a b ∈ˢ Sset IS.ω ⟩
opF5 a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (Fof-f5 a b) (op-in-J f5 a b a∈ b∈)

finSetMem : (n : ℕ) (h : Fin n → S) → ((i : Fin n) → ⟨ h i ∈ˢ Sset IS.ω ⟩)
          → ⟨ finSet n h ∈ˢ Sset IS.ω ⟩
finSetMem zero h hin = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (finSet0∅ h)) ∅∈Ssetω
finSetMem (suc n) h hin =
  subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (finSetSuc n h)) big
  where
  S1 : S
  S1 = F0 (h zero) (h zero)
  X : S
  X = finSet n (h ∘ suc)
  S1∈ : ⟨ S1 ∈ˢ Sset IS.ω ⟩
  S1∈ = opF0 (h zero) (h zero) (hin zero) (hin zero)
  X∈ : ⟨ X ∈ˢ Sset IS.ω ⟩
  X∈ = finSetMem n (h ∘ suc) (λ i → hin (suc i))
  big : ⟨ F5 (F0 S1 X) (h zero) ∈ˢ Sset IS.ω ⟩
  big = opF5 (F0 S1 X) (h zero) (opF0 S1 X S1∈ X∈) (hin zero)

finiteMember : (y : S) → Tally y → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ Sset IS.ω ⟩)
             → ⟨ y ∈ˢ Sset IS.ω ⟩
finiteMember y t y⊆ =
  subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym y≡finSet)
    (finSetMem (Tally.size t) (Tally.item t)
      (λ i → y⊆ (Tally.item t i) (Tally.inside t i)))
  where
  y≡finSet : y ≡ finSet (Tally.size t) (Tally.item t)
  y≡finSet = ext-⊆ sub sup
    where
    sub : (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ finSet (Tally.size t) (Tally.item t) ⟩
    sub z z∈ = PT.rec (snd (z ∈ˢ finSet (Tally.size t) (Tally.item t)))
      (λ { (i , q) → finSet-in (Tally.size t) (Tally.item t) z ∣ i , q ∣₁ })
      (Tally.onto t z z∈)
    sup : (z : S) → ⟨ z ∈ˢ finSet (Tally.size t) (Tally.item t) ⟩ → ⟨ z ∈ˢ y ⟩
    sup z z∈ = PT.rec (snd (z ∈ˢ y))
      (λ { (i , q) → subst (λ w → ⟨ w ∈ˢ y ⟩) q (Tally.inside t i) })
      (finSet-out (Tally.size t) (Tally.item t) z z∈)
```

<!--en-->
## The power obligation at a finite carrier
<!--zh-->
## 有穷载体处的幂义务
<!--/-->

<!--en-->
The L-side twin already delivers the finiteness of the constructible stages and
the fact that a tallied stage has only definable subsets: a tally of the
carrier, and the mask machinery that turns a subset into the finite table of
its selected names. What is new is the S-side reading. Fix a finite carrier
`Lset (# k)` that the tower holds. Every part of a mask is a finite table of
members of the carrier, hence a finite table of members of `Sset ω`, so the
table lemma places each part in the level. The collection of parts is itself a
finite table of members of the level, so the table lemma places the collection
in the level as well. The definable power of the carrier is exactly that
collection, by the mask round trip in one direction and the definability of
every part in the other. That is the power obligation: the definable power of a
finite carrier that the tower holds is again held by the tower.
<!--zh-->
L 侧孪生章已经交付可构造阶段的有穷性，以及「已清点阶段只有可定义子集」的事实：载体的点名册，以及把子集变成其被选名字的有穷表的掩码机器。新的是 S 侧读法。固定塔所收下的一个有穷载体 `Lset (# k)`。每个掩码的 `part` 都是载体成员所成的有穷表，从而是 `Sset ω` 成员所成的有穷表，故表引理把每个 `part` 放进该层。诸 `part` 的全体自身是层成员所成的有穷表，故表引理也把全体放进该层。载体的可定义幂恰是那个全体，一个方向用掩码来回，另一个方向用每个 `part` 的可定义性。这就是幂义务：塔收下的有穷载体的可定义幂，仍被塔收下。
<!--/-->

```agda
module Power (k : ℕ) (C∈J : ⟨ Lset (IS.# k) ∈ˢ Sset IS.ω ⟩) where
  σ : S
  σ = IS.# k
  oσ : IsOrd σ
  oσ = numeral-ord k
  t : Tally (Lset σ)
  t = go (stageOrder k)
    where
    go : StageOrder k → Tally (Lset σ)
    go (record { tally = t' ; tri = _ ; trans = _ }) = t'
  module PS = PowerStep σ oσ t

  carrier : (w : S) → ⟨ w ∈ˢ Lset σ ⟩ → ⟨ w ∈ˢ Sset IS.ω ⟩
  carrier w w∈L = Sset-trans IS.ω {x = Lset σ} {y = w} w∈L C∈J

  part-in-J : (v : Vec Bool (Tally.size t)) → ⟨ PS.part v ∈ˢ Sset IS.ω ⟩
  part-in-J v =
    finSetMem (PS.chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (PS.chosen v .snd j))
      (λ j → carrier (⟪ Lset σ ⟫↪ (PS.chosen v .snd j))
        (∈∈ₛ {a = ⟪ Lset σ ⟫↪ (PS.chosen v .snd j)} {b = Lset σ} .snd
          (∈ₛ⟪ Lset σ ⟫↪ (PS.chosen v .snd j))))

  M : ℕ
  M = maskCount (Tally.size t)
  fam : Fin M → S
  fam j = PS.part (maskAt (Tally.size t) j)

  defPow≡finSet : 𝒟ₒ (Lset σ) ≡ finSet M fam
  defPow≡finSet = ext-⊆ sub sup
    where
    sub : (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩ → ⟨ y ∈ˢ finSet M fam ⟩
    sub y y∈ = finSet-in M fam y ∣ mo .fst
      , (cong PS.part (mo .snd) ∙ PS.part-mask y y∈) ∣₁
      where
      mo : Σ[ j ∈ Fin M ] (maskAt (Tally.size t) j ≡ PS.maskOf y)
      mo = mask-onto (Tally.size t) (PS.maskOf y)
    sup : (y : S) → ⟨ y ∈ˢ finSet M fam ⟩ → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩
    sup y y∈ = PT.rec (snd (y ∈ˢ 𝒟ₒ (Lset σ))) go (finSet-out M fam y y∈)
      where
      go : Σ[ j ∈ Fin M ] (fam j ≡ y) → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩
      go (j , q) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset σ) ⟩) q
        (PS.part-def (maskAt (Tally.size t) j))

  defPow∈J : ⟨ 𝒟ₒ (Lset σ) ∈ˢ Sset IS.ω ⟩
  defPow∈J = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym defPow≡finSet)
    (finSetMem M fam (λ j → part-in-J (maskAt (Tally.size t) j)))

basePow : (k : ℕ) → ⟨ Lset (IS.# k) ∈ˢ Sset IS.ω ⟩
        → ⟨ 𝒟ₒ (Lset (IS.# k)) ∈ˢ Sset IS.ω ⟩
basePow k C∈J = Power.defPow∈J k C∈J
```

<!--en-->
## The base-block instance
<!--zh-->
## 基块实例
<!--/-->

<!--en-->
The instance is assembled in the shape DefInJ's discharge consumes: a member of
`ω` is merely a numeral, so the power obligation at that numeral, transported
across the numeral equality, gives the definable power of the constructible
stage at `ζ`; and the successor collapse identifies that power with the stage
one step up. This is exactly the `γ = ω` instance of the discharge's
conclusion, and the fragment witness at that single point is the identity
fragment: the definable power itself, which is now known to be a member. The
sharpened limit form is not available here, since `ω` has no limit below it;
the direct finiteness proof is the whole content.
<!--zh-->
实例按 DefInJ 兑付所消费的形状装配：`ω` 的成员仅仅是某个数码，故该数码处的幂义务经数码等式搬运，给出 `ζ` 处可构造阶段的可定义幂；后继坍缩再把该幂认同为再上一层的阶段。这正是兑付结论在 `γ = ω` 处的实例，而该单点处的片段见证是恒等片段：可定义幂自身，它现已确知为成员。加锐的极限形式此处不可用，因为 `ω` 之下没有极限；直接的有穷性证明就是全部内容。
<!--/-->

```agda
baseDefPow : (ζ : S) → ⟨ ζ ∈ˢ IS.ω ⟩ → ⟨ Lset ζ ∈ˢ Sset IS.ω ⟩
           → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω ⟩
baseDefPow ζ ζ∈ω L∈ = PT.rec (snd (𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω)) go ζ∈ω
  where
  go : Σ[ k ∈ Lift ℕ ] (IS.# (lower k) ≡ ζ) → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω ⟩
  go (k , q) = subst (λ w → ⟨ 𝒟ₒ w ∈ˢ Sset IS.ω ⟩) (cong Lset q)
    (Power.defPow∈J (lower k) L∈k)
    where
    L∈k : ⟨ Lset (IS.# (lower k)) ∈ˢ Sset IS.ω ⟩
    L∈k = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (cong Lset q)) L∈

baseStage∈J : (ζ : S) → ⟨ ζ ∈ˢ IS.ω ⟩ → ⟨ Lset ζ ∈ˢ Sset IS.ω ⟩
            → ⟨ Lset (IS.sucV ζ) ∈ˢ Sset IS.ω ⟩
baseStage∈J ζ ζ∈ω L∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (Lset-suc ζ))
  (baseDefPow ζ ζ∈ω L∈)

baseFragment : (ζ : S) → ⟨ ζ ∈ˢ IS.ω ⟩ → ⟨ Lset ζ ∈ˢ Sset IS.ω ⟩
             → ∥ Σ[ F ∈ S ] ( ⟨ F ∈ˢ Sset IS.ω ⟩
               × (((y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ y ∈ˢ F ⟩)
               × ((y : S) → ⟨ y ∈ˢ F ⟩
                 → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ Lset ζ ⟩)
                 → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩))) ∥₁
baseFragment ζ ζ∈ω L∈ = ∣ 𝒟ₒ (Lset ζ)
  , ( baseDefPow ζ ζ∈ω L∈
    , ( (λ y y∈ → y∈) , (λ y y∈ _ → y∈) ) ) ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The base block is closed. `limω` supplies the limit predicate the tower's
machinery asks for at the first limit. The S-side tally runs the step's finite
square and certifies that every finite stage of the rud tower is finite. The
table lemma, through the limit level's closure under the basis operations,
places every finite set of members of `Sset ω` back into `Sset ω`, and the
power module reads the definable power of a held finite carrier as such a
finite collection. `baseStage∈J` is the discharge's conclusion at `γ = ω`, and
`baseFragment` is the identity-fragment witness at that point: the residue
DefInJ left standing, closed at the first limit by hereditary finiteness.
<!--zh-->
基块关闭。`limω` 供给塔的机器在第一个极限处索要的极限谓词。S 侧点名册跑过 step 的有限平方，证明初步塔的每个有穷阶段都有穷。表引理经极限层对基底运算的封闭，把 `Sset ω` 成员所成的每个有穷集合放回 `Sset ω`；幂模块把塔所收的有穷载体的可定义幂读作这样一个有穷集合。`baseStage∈J` 即兑付结论在 `γ = ω` 处的形式，`baseFragment` 是该点处的恒等片段见证：DefInJ 留下的存留，在第一个极限处由遗传有穷性关闭。
<!--/-->
