# The bridge between the two towers

<!--en-->
Gödel's definition and Jensen's definition meet here. The constructible tower
takes definable subsets at every stage; the rud tower takes one closure step at
every stage and collects at limits. This chapter connects the two surfaces at
the level of single steps, in both directions, and records exactly what a
per-level identification of the towers still costs.
<!--zh-->
哥德尔的定义与 Jensen 的定义在此相遇。可构造塔在每个阶段取可定义子集，初步函数塔在每个阶段走一步闭包、在极限处收拢。本章在单步的层面双向连接两个表面，并如实记下逐层认同两塔仍需付出的代价。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.Bridge {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-in; Lset-out; Lset-mono; Lset-layer; layer-trans
  ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; isL; Lset→isL )
open import L.Rud.Ops {ℓ} using ( F0; F0-spec; F1; F2; F3; F4; F5; F6; F7 )
open import L.Rud.Images {ℓ} using ( F8; F10; left; right; module F15Of )
open import L.Rud.Describe {ℓ} using
  ( module F0Desc; module F1Desc; module F2Desc; module F3Desc; module F4Desc
  ; module F5Desc; module F6Desc; module F7Desc; module F8Desc
  ; module F10Desc )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; Fof; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5
  ; Fof-f6; Fof-f7; Fof-f8; Fof-f9; Fof-f10; Fof-f11; Fof-f12; Fof-f13
  ; Fof-f14; Fof-f15; F15A; singl≡pair
  ; Sset; Sset-trans; Sset-out; Sset-mem; Sset-suc
  ; Jset; Jset-rud; limit-succ-mem
  ; step; step-out; StepArm; arm-member; arm-self; arm-image )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; limit-mem-ord; isSucc; ord-case )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-mem; +ω-limit )
open import L.Rud.ClassJ {ℓ} lem A using ( isJ; Jset→isJ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.Switch {ℓ} lem A using ( module Descr; module Hops )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## One Def step, read twice
<!--zh-->
## 一步 Def，读两遍
<!--/-->

<!--en-->
The definable power of a stage is the next stage's first summand, and the stage
itself is one of its own definable subsets, described by the true formula. Both
readings are one line, and together they say the tower's levels are its own
members one step later.
<!--zh-->
一个阶段的可定义幂是下一阶段的头一个被并项，而阶段自身就是自己的一个可定义子集，由真公式描述。两处读法各一行，合起来说：塔的层在一步之后成为自己的成员。
<!--/-->

```agda
𝒟ₒ⊆Lsuc : (ξ x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset ξ) ⟩ → ⟨ x ∈ˢ Lset (sucV ξ) ⟩
𝒟ₒ⊆Lsuc ξ x h = Lset-in (sucV ξ) ξ x (self∈sucV ξ) h

Lset∈Lsuc : (ξ : S) → ⟨ Lset ξ ∈ˢ Lset (sucV ξ) ⟩
Lset∈Lsuc ξ = 𝒟ₒ⊆Lsuc ξ (Lset ξ) (𝒟ₒ-intro (Lset ξ) (Lset ξ)
  ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset ξ) ∣₁)
```

<!--en-->
## A Def step lands in the rud tower
<!--zh-->
## 一步 Def 落入初步函数塔
<!--/-->

<!--en-->
The satisfaction-set engine is abstract in its transitive carrier: it needs the
carrier to be transitive, the receiving class to be transitive and closed under
the sixteen operations, and the carrier itself to be a member of the class. A
limit level of the rud tower is such a class, so every definable subset of a
constructible stage that the rud tower already contains as a member lands in
that limit level. The membership hypothesis is a variable, never a transported
one, which is what keeps the union tower out of conversion position.
<!--zh-->
满足集引擎对其传递载体是抽象的：它要求载体传递、接收类传递且对十六个运算封闭，且载体自身是类的成员。初步函数塔的极限层正是这样的类，故初步函数塔已经把某个可构造阶段作为成员收下之后，该阶段的每个可定义子集都落进那个极限层。隶属假设取变量，绝不取搬运而来者，这正是把并塔挡在转换位置之外的办法。
<!--/-->

```agda
Ldef→J : (β γ : S) → (limγ : ⟨ isLimit γ ⟩)
       → ⟨ Lset β ∈ˢ Jset γ limγ ⟩
       → (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩ → ⟨ x ∈ˢ Jset γ limγ ⟩
Ldef→J β γ limγ L∈J x x∈𝒟 =
  PT.rec (snd (x ∈ˢ Jset γ limγ)) go (𝒟ₒ-inv (Lset β) x x∈𝒟)
  where
  Utr : (u v : S) → ⟨ u ∈ˢ v ⟩ → ⟨ v ∈ˢ Lset β ⟩ → ⟨ u ∈ˢ Lset β ⟩
  Utr u v u∈v v∈L = layer-trans (Lset-layer β) {x = v} {y = u} u∈v v∈L
  Jtr : (u v : S) → ⟨ v ∈ˢ Jset γ limγ ⟩ → ⟨ u ∈ˢ v ⟩ → ⟨ u ∈ˢ Jset γ limγ ⟩
  Jtr u v v∈J u∈v = Sset-trans γ {x = v} {y = u} u∈v v∈J
  module Sβ = Sat (Lset β) Utr (λ z → ⟨ z ∈ˢ Jset γ limγ ⟩) Jtr
                  (Jset-rud γ limγ) L∈J
  go : Σ[ φ ∈ Formula ⟪ Lset β ⟫ 1 ] (DefOf.defSet (Lset β) φ ≡ x)
     → ⟨ x ∈ˢ Jset γ limγ ⟩
  go (φ , eq) = subst (λ w → ⟨ w ∈ˢ Jset γ limγ ⟩) eq (Sβ.defSet-InJ φ)
```

<!--en-->
## The sixteen values over a transitive carrier
<!--zh-->
## 传递载体上的十六个值
<!--/-->

<!--en-->
The junk absorption asks the opposite question to the switch chapter's: not
whether a value of the sixteen operations sits inside one closed level, but
whether it is **definable** over a transitive set that already holds both
arguments. Over a level the description chapter's arms were never needed for
plain arguments, because the level's own rud closure answered first; here there
is no such closure to lean on, so every arm is the genuine description. The
statement is the description chapter's `Arm`{.Agda} shape at an arbitrary
transitive carrier: given that the value is a subset of the carrier, produce a
formula whose definable subset is that value. Six of the sixteen are pairs of
two named sets and go through the pairing arm, and the relativization slot is
the one side condition, exactly as in the level chapter.
<!--zh-->
垃圾吸收所问与领悟章相反：不是问十六运算的某个值是否落在某个封闭的层里，而是问它在一个已经收下两个实参的传递集上是否**可定义**。在层上，平实参从来用不到描述章的诸臂，因为层自身的初步闭包先一步作答；此处没有那样的闭包可倚，故每条臂都是货真价实的描述。陈述取描述章 `Arm`{.Agda} 的形状，但落在任意传递载体上：给定该值是载体的子集，造出一条公式，其可定义子集恰是该值。十六个中有六个是两个指名集合之对，走配对臂，而相对化槽是唯一的附带条件，与层章完全一致。
<!--/-->

```agda
module Arms (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C)) where

  module Ds = Descr C Ctr
  module SemC = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemC.At (⟪ C ⟫) (⟪ C ⟫↪) using ( _⊨_ )

  Arm : S → Type (ℓ-suc ℓ)
  Arm W = ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
        → Σ[ Φ ∈ Formula ⟪ C ⟫ 1 ] (Ds.Defu.defSet Φ ≡ W)

  reshape : {W W' : S} → W ≡ W' → Arm W' → Arm W
  reshape {W} {W'} e f sub = r .fst , r .snd ∙ sym e
    where
    r : Σ[ Φ ∈ Formula ⟪ C ⟫ 1 ] (Ds.Defu.defSet Φ ≡ W')
    r = f (λ v h → sub v (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym e) h))

  pairArm : (c d : S) → Arm (F0 c d)
  pairArm c d sub = D.Φ₀ , D.F0-defSet≡
    where
    c∈ : ⟨ c ∈ˢ C ⟩
    c∈ = sub c (F0-spec c d c .snd ∣ inl refl ∣₁)
    d∈ : ⟨ d ∈ˢ C ⟩
    d∈ = sub d (F0-spec c d d .snd ∣ inr refl ∣₁)
    module D = F0Desc C c d c∈ d∈ Ctr

  module F15C = F15Of A

  relArm : (a : S) → ⟨ a ∈ˢ C ⟩ → ⟨ A ∈ˢ C ⟩ → Arm (F15A a)
  relArm a a∈ A∈C sub = Φ , Ds.described (F15A a) Φ dΦ sub din dout
    where
    fibA : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ A)
    fibA = ∈-asFiber {a = A} {b = C} A∈C
    fiba : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ a)
    fiba = ∈-asFiber {a = a} {b = C} a∈
    Φ : Formula ⟪ C ⟫ 1
    Φ = (var zero ∈̇ con (fiba .fst)) ∧̇ (var zero ∈̇ con (fibA .fst))
    dΦ : Δ₀ Φ
    dΦ = δ-∧ δ-∈ δ-∈
    din : (v : S) → ⟨ v ∈ˢ F15A a ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
    din v h = ( subst (λ t → ⟨ v ∈ˢ t ⟩) (sym (fiba .snd)) (parts .fst)
              , subst (λ t → ⟨ v ∈ˢ t ⟩) (sym (fibA .snd)) (parts .snd) )
      where
      parts : ⟨ v ∈ˢ a ⟩ × ⟨ v ∈ˢ A ⟩
      parts = subst ⟨_⟩ (F15C.F15-spec a v) h
    dout : (v : S) → ⟨ v ∈ˢ C ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ F15A a ⟩
    dout v _ (h₁ , h₂) = subst ⟨_⟩ (sym (F15C.F15-spec a v))
      ( subst (λ t → ⟨ v ∈ˢ t ⟩) (fiba .snd) h₁
      , subst (λ t → ⟨ v ∈ˢ t ⟩) (fibA .snd) h₂ )

  imgArm : ⟨ A ∈ˢ C ⟩ → (i : Op16) (a b : S)
         → ⟨ a ∈ˢ C ⟩ → ⟨ b ∈ˢ C ⟩ → Arm (Fof i a b)
  imgArm hA op0 a b a∈ b∈ = reshape (Fof-f0 a b) (pairArm a b)
  imgArm hA op1 a b a∈ b∈ = reshape (Fof-f1 a b) arm
    where
    module D = F1Desc C a b a∈ b∈ Ctr
    arm : Arm (F1 a b)
    arm sub = D.Φ₁ , D.F1-defSet≡
  imgArm hA op2 a b a∈ b∈ = reshape (Fof-f2 a b) arm
    where
    module D = F2Desc C a b a∈ b∈
    module H = Hops C a b a∈ b∈ Ctr
    arm : Arm (F2 a b)
    arm sub = D.Φ₂ , Ds.described (F2 a b) D.Φ₂ D.dΦ₂ sub
      D.F2-desc-in (λ v _ h → H.F2-desc-out v h)
  imgArm hA op3 a b a∈ b∈ = reshape (Fof-f3 a b) arm
    where
    module D = F3Desc C a b a∈ b∈
    module H = Hops C a b a∈ b∈ Ctr
    arm : Arm (F3 a b)
    arm sub = D.Φ₃ , Ds.described (F3 a b) D.Φ₃ D.dΦ₃ sub
      D.F3-desc-in (λ v _ h → H.F3-desc-out v h)
  imgArm hA op4 a b a∈ b∈ = reshape (Fof-f4 a b) arm
    where
    module D = F4Desc C a b a∈ b∈
    module H = Hops C a b a∈ b∈ Ctr
    arm : Arm (F4 a b)
    arm sub = D.Φ₄ , Ds.described (F4 a b) D.Φ₄ D.dΦ₄ sub
      D.F4-desc-in (λ v _ h → H.F4-desc-out v h)
  imgArm hA op5 a b a∈ b∈ = reshape (Fof-f5 a b) arm
    where
    module D = F5Desc C a b a∈ Ctr
    arm : Arm (F5 a b)
    arm sub = D.Φ₅ , D.F5-defSet≡
  imgArm hA op6 a b a∈ b∈ = reshape (Fof-f6 a b) arm
    where
    module D = F6Desc C a b a∈ Ctr
    module H = Hops C a b a∈ b∈ Ctr
    arm : Arm (F6 a b)
    arm sub = D.Φ₆ , Ds.described (F6 a b) D.Φ₆ D.dΦ₆ sub
      D.F6-desc-in (λ v _ h → H.F6-desc-out v h)
  imgArm hA op7 a b a∈ b∈ = reshape (Fof-f7 a b) arm
    where
    module D = F7Desc C a b a∈
    module H = Hops C a b a∈ b∈ Ctr
    arm : Arm (F7 a b)
    arm sub = D.Φ₇ , Ds.described (F7 a b) D.Φ₇ D.dΦ₇ sub
      D.F7-desc-in (λ v _ h → H.F7-desc-out v h)
  imgArm hA op8 a b a∈ b∈ = reshape (Fof-f8 a b) arm
    where
    module D = F8Desc C a b a∈ b∈ Ctr
    arm : Arm (F8 a b)
    arm sub = D.Φ₈ , D.F8-defSet≡
      (λ w w∈ₛ → ∈∈ₛ {a = w} {b = C} .fst
        (sub w (∈∈ₛ {a = w} {b = F8 a b} .snd w∈ₛ)))
  imgArm hA op9 a b a∈ b∈ =
    reshape (Fof-f9 a b) (pairArm (⁅ a ⁆s) (⁅ a , b ⁆))
  imgArm hA op10 a b a∈ b∈ = reshape (Fof-f10 a b) arm
    where
    module D = F10Desc C a b a∈ b∈ Ctr
    arm : Arm (F10 a b)
    arm sub = D.Φ₁₀ , D.F10-defSet≡
  imgArm hA op11 a b a∈ b∈ = reshape (Fof-f11 a b)
    (pairArm (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆))
  imgArm hA op12 a b a∈ b∈ = reshape (Fof-f12 a b)
    (pairArm (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆))
  imgArm hA op13 a b a∈ b∈ = reshape (Fof-f13 a b)
    (pairArm (left b) (pr (right b) a))
  imgArm hA op14 a b a∈ b∈ = reshape (Fof-f14 a b)
    (pairArm (left b) (pr a (right b)))
  imgArm hA op15 a b a∈ b∈ = reshape (Fof-f15 a b) (relArm a a∈ hA)
```

<!--en-->
## The junk lands one step up
<!--zh-->
## 垃圾上升一步落地
<!--/-->

<!--en-->
The arms read at a constructible stage give the honest offset. A value of the
sixteen operations lands in the **next** stage as soon as one stage holds both
arguments and every member of the value; nothing further is needed and nothing
less will do, since the value must be a subset of the carrier its formula
speaks about. Two stages are therefore in play, not one: the arguments' stage,
and the stage that already holds the value's members. At a limit index the two
collapse, which is the reason the bridge reads the tower at limits.
<!--zh-->
在可构造阶段处读出的诸臂给出如实的偏移。只要有一个阶段同时收下两个实参与该值的每个成员，十六运算的值就落在**下一个**阶段；再多不必，再少不行，因为值必须是其公式所谈论的那个载体的子集。故在场的是两个阶段而非一个：实参所在的阶段，以及已经收下值之诸成员的阶段。在极限索引处二者合一，这正是桥在极限处读塔的理由。
<!--/-->

```agda
Ltr : (ξ : S) → Transitive 𝒮ᵥ (λ x → x ∈ˢ Lset ξ)
Ltr ξ = layer-trans (Lset-layer ξ)

Lval : (ζ : S) → ⟨ A ∈ˢ Lset ζ ⟩ → (i : Op16) (a b : S)
     → ⟨ a ∈ˢ Lset ζ ⟩ → ⟨ b ∈ˢ Lset ζ ⟩
     → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
     → ⟨ Fof i a b ∈ˢ Lset (sucV ζ) ⟩
Lval ζ hA i a b a∈ b∈ sub = 𝒟ₒ⊆Lsuc ζ (Fof i a b)
  (𝒟ₒ-intro (Lset ζ) (Fof i a b) ∣ r .fst , r .snd ∣₁)
  where
  module Aζ = Arms (Lset ζ) (Ltr ζ)
  r : Σ[ Φ ∈ Formula ⟪ Lset ζ ⟫ 1 ] (DefOf.defSet (Lset ζ) Φ ≡ Fof i a b)
  r = Aζ.imgArm hA i a b a∈ b∈ sub

Lpair : (ζ p q : S) → ⟨ p ∈ˢ Lset ζ ⟩ → ⟨ q ∈ˢ Lset ζ ⟩
      → ⟨ F0 p q ∈ˢ Lset (sucV ζ) ⟩
Lpair ζ p q p∈ q∈ = 𝒟ₒ⊆Lsuc ζ (F0 p q)
  (𝒟ₒ-intro (Lset ζ) (F0 p q) ∣ r .fst , r .snd ∣₁)
  where
  module Aζ = Arms (Lset ζ) (Ltr ζ)
  sub : (v : S) → ⟨ v ∈ˢ F0 p q ⟩ → ⟨ v ∈ˢ Lset ζ ⟩
  sub v h = PT.rec (snd (v ∈ˢ Lset ζ)) go (F0-spec p q v .fst h)
    where
    go : (v ≡ p) ⊎ (v ≡ q) → ⟨ v ∈ˢ Lset ζ ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym e) p∈
    go (inr e) = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym e) q∈
  r : Σ[ Φ ∈ Formula ⟪ Lset ζ ⟫ 1 ] (DefOf.defSet (Lset ζ) Φ ≡ F0 p q)
  r = Aζ.pairArm p q sub
```

<!--en-->
## A common stage, and pairing inside a limit
<!--zh-->
## 共同阶段，与极限内部的配对
<!--/-->

<!--en-->
A member of a limit stage already sits in an earlier stage, one step below the
one it entered at, and two members share such a stage by the trichotomy of the
indices. Pairing is then closed **inside** the limit: form the pair one stage
above the shared one, and the limit contains that successor. The Kuratowski
pair follows by two pairings, so a limit stage holds the pairs of its members,
which is exactly the subset condition the pair-valued operations need.
<!--zh-->
极限阶段的成员早已落在更早的阶段里，即它进场处的下一阶段；而由索引的三歧，两个成员共享这样一个阶段。配对于是在极限**内部**封闭：在共享阶段之上一层造出对，而极限含有那个后继。Kuratowski 对经两次配对而来，故极限阶段收下其成员之对，这恰是对值运算所需的那条子集条件。
<!--/-->

```agda
Lstage : (γ : S) → ⟨ isLimit γ ⟩ → (x : S) → ⟨ x ∈ˢ Lset γ ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩) ∥₁
Lstage γ limγ x x∈ = PT.map go (Lset-out γ x x∈)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
     → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩)
  go (δ , δ∈γ , h) = sucV δ , (limit-succ-mem γ δ limγ δ∈γ , 𝒟ₒ⊆Lsuc δ x h)

Lstage₂ : (γ : S) → ⟨ isLimit γ ⟩ → (x y : S)
        → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩) ∥₁
Lstage₂ γ limγ x y x∈ y∈ = PT.rec squash₁
  (λ px → PT.map (both px) (Lstage γ limγ y y∈)) (Lstage γ limγ x x∈)
  where
  G : Type (ℓ-suc ℓ)
  G = Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩)
  both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩)
       → Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ γ ⟩ × ⟨ y ∈ˢ Lset ζ ⟩) → G
  both (ξ , ξ∈γ , x∈ξ) (ζ , ζ∈γ , y∈ζ) = go (ord-tri ξ (oo ξ ξ∈γ) ζ (oo ζ ζ∈γ))
    where
    oo : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ
    oo δ δ∈γ = limit-mem-ord γ limγ δ δ∈γ
    go : Tri ξ ζ → G
    go (inl ξ∈ζ) = ζ , (ζ∈γ , (Lset-mono {α = ζ} {β = ξ} ξ∈ζ x∈ξ , y∈ζ))
    go (inr (inl ξ≡ζ)) = ζ
      , (ζ∈γ , (subst (λ w → ⟨ x ∈ˢ Lset w ⟩) ξ≡ζ x∈ξ , y∈ζ))
    go (inr (inr ζ∈ξ)) = ξ , (ξ∈γ , (x∈ξ , Lset-mono {α = ξ} {β = ζ} ζ∈ξ y∈ζ))

Lpair-limit : (γ : S) → ⟨ isLimit γ ⟩ → (p q : S)
            → ⟨ p ∈ˢ Lset γ ⟩ → ⟨ q ∈ˢ Lset γ ⟩ → ⟨ F0 p q ∈ˢ Lset γ ⟩
Lpair-limit γ limγ p q p∈ q∈ = PT.rec (snd (F0 p q ∈ˢ Lset γ)) go
  (Lstage₂ γ limγ p q p∈ q∈)
  where
  go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ p ∈ˢ Lset ξ ⟩ × ⟨ q ∈ˢ Lset ξ ⟩)
     → ⟨ F0 p q ∈ˢ Lset γ ⟩
  go (ξ , ξ∈γ , p∈ξ , q∈ξ) =
    Lset-mono {α = γ} {β = sucV ξ} (limit-succ-mem γ ξ limγ ξ∈γ)
      (Lpair ξ p q p∈ξ q∈ξ)

Lpr-limit : (γ : S) → ⟨ isLimit γ ⟩ → (p q : S)
          → ⟨ p ∈ˢ Lset γ ⟩ → ⟨ q ∈ˢ Lset γ ⟩ → ⟨ pr p q ∈ˢ Lset γ ⟩
Lpr-limit γ limγ p q p∈ q∈ =
  Lpair-limit γ limγ (⁅ p ⁆s) (⁅ p , q ⁆) sing∈ pair∈
  where
  sing∈ : ⟨ ⁅ p ⁆s ∈ˢ Lset γ ⟩
  sing∈ = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (singl≡pair p))
    (Lpair-limit γ limγ p p p∈ p∈)
  pair∈ : ⟨ ⁅ p , q ⁆ ∈ˢ Lset γ ⟩
  pair∈ = Lpair-limit γ limγ p q p∈ q∈
```

<!--en-->
## The junk of a rud step, absorbed
<!--zh-->
## 一步初步函数的垃圾，被吸收
<!--/-->

<!--en-->
Now the junk itself. A rud step over a set `U` adds the values of the sixteen
operations at arguments drawn from `U ∪ {U}`, and the argument that is `U`
itself is what no lemma about subsets of `U` can reach. Read against the
constructible tower the distinction disappears: as soon as a stage holds `U` as
a **member**, both kinds of argument are ordinary members of that stage, and the
value is definable there. That is the whole content of the absorption, and its
offset is one stage.
<!--zh-->
现在轮到垃圾本身。`U` 之上一步初步函数，添入十六运算在取自 `U ∪ {U}` 的实参处的诸值，而那个等于 `U` 自身的实参，是任何关于 `U` 之子集的引理都够不到的。对着可构造塔来读，这道分别就消失了：只要某个阶段把 `U` 作为**成员**收下，两种实参都是该阶段的寻常成员，值在那里可定义。这就是吸收的全部内容，其偏移为一个阶段。
<!--/-->

```agda
Ljunk : (ζ : S) → ⟨ A ∈ˢ Lset ζ ⟩ → (U : S) → ⟨ U ∈ˢ Lset ζ ⟩
      → (i : Op16) (a b : S)
      → (⟨ a ∈ˢ U ⟩ ⊎ (a ≡ U)) → (⟨ b ∈ˢ U ⟩ ⊎ (b ≡ U))
      → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
      → ⟨ Fof i a b ∈ˢ Lset (sucV ζ) ⟩
Ljunk ζ hA U U∈ i a b sa sb sub =
  Lval ζ hA i a b (split a sa) (split b sb) sub
  where
  split : (c : S) → (⟨ c ∈ˢ U ⟩ ⊎ (c ≡ U)) → ⟨ c ∈ˢ Lset ζ ⟩
  split c (inl c∈U) = Ltr ζ {x = U} {y = c} c∈U U∈
  split c (inr c≡U) = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym c≡U) U∈
```

<!--en-->
## The bridge

The two towers are identified where both are read at the same limit index. That
identification is the one thing this chapter does not prove: it is taken here as
a hypothesis, named once, and everything the next chapters want follows from it
in a few lines. The endpoints are the two class predicates: constructible in
Gödel's sense, and constructible in Jensen's. Going right, a constructible set
sits in an ordinal stage, the `ω`-extension of that ordinal is a limit above it,
and the identification reads the stage as a rud level. Going left, a rud level
is an ordinal stage on the nose, and the limit certificate already carries the
ordinality the constructible predicate asks for.
<!--zh-->
## 桥

两塔在同一极限索引处被同时读出之处认同。这项认同正是本章唯一未证之事：此处取作假设，一次具名，而后续诸章所要的一切都由它数行导出。两端是两个类谓词：哥德尔意义下的可构造，与 Jensen 意义下的可构造。向右走，可构造集落在某个序数阶段里，该序数的 `ω` 延拓是其上的极限，认同把该阶段读作初步函数层。向左走，初步函数层原样就是序数阶段，而极限证书早已带着可构造谓词所要的序数性。
<!--/-->

```agda
Matching : Type (ℓ-suc ℓ)
Matching = (γ : S) → (limγ : ⟨ isLimit γ ⟩) → Lset γ ≡ Jset γ limγ

module Bridged (match : Matching) where

  bridge-isL→isJ : (x : S) → ⟨ isL x ⟩ → ⟨ isJ x ⟩
  bridge-isL→isJ x = PT.rec (snd (isJ x)) go
    where
    go : Σ[ α ∈ S ] (IsOrd α × ⟨ x ∈ˢ Lset α ⟩) → ⟨ isJ x ⟩
    go (α , ordα , x∈L) = Jset→isJ (+ω α) limγ x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (match (+ω α) limγ)
        (Lset-mono {α = +ω α} {β = α} (+ω-mem α) x∈L))
      where
      limγ : ⟨ isLimit (+ω α) ⟩
      limγ = +ω-limit α ordα

  bridge-isJ→isL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩
  bridge-isJ→isL x = PT.rec (snd (isL x)) go
    where
    go : Σ[ γ ∈ S ] (Σ[ lim ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ˢ Jset γ lim ⟩) → ⟨ isL x ⟩
    go (γ , lim , x∈J) = Lset→isL γ (isLimit-ord γ lim) x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (match γ lim)) x∈J)

  bridge-level : (x : S) → ⟨ isL x ⟩
               → ∥ Σ[ γ ∈ S ] (Σ[ lim ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ˢ Jset γ lim ⟩) ∥₁
  bridge-level x x∈L = bridge-isL→isJ x x∈L

  level-bridge : (γ : S) → (lim : ⟨ isLimit γ ⟩) → (x : S)
               → ⟨ x ∈ˢ Jset γ lim ⟩ → ⟨ isL x ⟩
  level-bridge γ lim x x∈J = bridge-isJ→isL x (Jset→isJ γ lim x x∈J)
```

<!--en-->
## One rud step against a level the tower holds
<!--zh-->
## 与塔已收下之层相对的一步初步函数
<!--/-->

<!--en-->
Here is how the absorption is consumed, and it asks for less than one might
expect: no identification of the towers, only that some constructible stage
holds the rud level as a **member**. One rud step over that level is then read
arm by arm against the next stage. The members of the level are members of the
stage by transitivity, the level itself is a member outright, and each image
value is definable by the absorption. What the step still asks for is the subset
side, that each value's members are already in the stage; it is stated here as a
hypothesis, since discharging it means reading the member characterization of
each of the sixteen operations once. The pair-valued ones cost one stage more
than the flat ones, because their members are pairs, and pairing closes only
inside a limit. The matching below supplies the membership hypothesis at the
successor of the matched index, so the whole absorption sits two stages above a
matched limit, three for the pair-valued values, and all of it is absorbed by
the next limit stage.
<!--zh-->
吸收如何被消费，看这里，而它所索取的比预想的更少：不需要两塔的认同，只需要某个可构造阶段把初步函数层作为**成员**收下。那么该层之上一步初步函数便可逐臂对着下一个阶段读出：层的成员由传递性成为阶段的成员，层自身径直就是成员，而每个像值由吸收而可定义。这一步仍要索取的是子集一侧，即每个值的诸成员早已在该阶段之内；此处取作假设，因为清偿它意味着把十六个运算的成员刻画各读一遍。对值的那几个比平坦的那几个多花一个阶段，因为它们的成员是对，而配对只在极限内部封闭。下方的认同在已认同索引的后继处供应那条隶属假设，故整场吸收坐在已认同极限之上两个阶段，对值者三个，而这一切都被下一个极限阶段吸收。
<!--/-->

```agda
ValuesIn : (μ : S) → (limμ : ⟨ isLimit μ ⟩) → (ζ : S) → Type (ℓ-suc ℓ)
ValuesIn μ limμ ζ = (i : Op16) (a b : S)
  → (⟨ a ∈ˢ Jset μ limμ ⟩ ⊎ (a ≡ Jset μ limμ))
  → (⟨ b ∈ˢ Jset μ limμ ⟩ ⊎ (b ≡ Jset μ limμ))
  → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩

Lstep-absorb : (μ : S) → (limμ : ⟨ isLimit μ ⟩) → (ζ : S)
             → ⟨ A ∈ˢ Lset ζ ⟩ → ⟨ Jset μ limμ ∈ˢ Lset ζ ⟩
             → ValuesIn μ limμ ζ
             → (x : S) → ⟨ x ∈ˢ step (Jset μ limμ) ⟩ → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
Lstep-absorb μ limμ ζ hA U∈L vb x x∈step =
  PT.rec (snd (x ∈ˢ Lset (sucV ζ))) go (step-out (Jset μ limμ) x x∈step)
  where
  up : (y : S) → ⟨ y ∈ˢ Lset ζ ⟩ → ⟨ y ∈ˢ Lset (sucV ζ) ⟩
  up y h = Lset-mono {α = sucV ζ} {β = ζ} (self∈sucV ζ) h
  go : StepArm (Jset μ limμ) x → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
  go (arm-member x∈U) = up x (Ltr ζ {x = Jset μ limμ} {y = x} x∈U U∈L)
  go (arm-self x≡U) = up x
    (subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym x≡U) U∈L)
  go (arm-image i a b sa sb x≡) =
    subst (λ w → ⟨ w ∈ˢ Lset (sucV ζ) ⟩) (sym x≡)
      (Ljunk ζ hA (Jset μ limμ) U∈L i a b sa sb (vb i a b sa sb))

matched-level∈L : (μ : S) → (limμ : ⟨ isLimit μ ⟩) → Lset μ ≡ Jset μ limμ
                → ⟨ Jset μ limμ ∈ˢ Lset (sucV μ) ⟩
matched-level∈L μ limμ mt =
  subst (λ w → ⟨ w ∈ˢ Lset (sucV μ) ⟩) mt (Lset∈Lsuc μ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Both single steps are built. A definable subset of a constructible stage lands
in a limit level of the rud tower as soon as that stage is a **member** of the
level, which is the satisfaction-set engine read at a carrier that is not itself
a level. In the other direction, the sixteen operations are described over an
arbitrary transitive carrier, so a value whose arguments and members the carrier
holds is definable there, and the junk of a rud step, the values with the level
itself in an argument slot, is ordinary once a stage holds that level as a
member. The verified offset is therefore **two** stages above a matched limit
index: one to hold the level, one to define the value. Pairing is closed inside
a limit stage, which is the subset condition for the pair-valued operations.

What is not proved here is the identification of the two towers at limit
indices, and the reason is worth recording. Both directions of an interleaving
ask for the levels of one tower to be **members** of the other's, and each of
those is a definability statement about a hierarchy rather than about a single
step: on one side the rud step operator would have to be definable over a
constructible stage (which needs the graphs of the sixteen operations, not their
values), on the other the constructible stages would have to appear inside the
rud tower. The class equivalence is therefore packaged as a module over the
identification, so that discharging one hypothesis delivers both endpoints.
<!--zh-->
两个单步都已造出。可构造阶段的一个可定义子集，只要该阶段是初步函数塔某极限层的**成员**，就落进那个极限层，这是把满足集引擎读在一个自身并非层的载体上。反方向，十六个运算在任意传递载体上都有描述，故载体既收下实参又收下诸成员的那个值在其上可定义；而一步初步函数的垃圾，即实参槽里坐着层自身的那些值，一旦某个阶段把该层作为成员收下便成了寻常之物。故经核实的偏移是已认同的极限索引之上**两**个阶段：一个用来收下层，一个用来定义值。配对在极限阶段内部封闭，这正是对值运算所需的子集条件。

此处未证的是两塔在极限索引处的认同，而其缘由值得记下。交错的两个方向都要求一塔的诸层是另一塔的**成员**，而这两件事都是关于层级而非关于单步的可定义性陈述：一侧要求初步函数的 step 算子在可构造阶段上可定义 (那需要十六运算的图，而非它们的值)，另一侧要求可构造诸阶段出现在初步函数塔之内。故类的等价打包成认同之上的模块，只要清偿一条假设，两端一并交付。
<!--/-->

<!--en-->
## The empty stage, and one rud step at an arbitrary set
<!--zh-->
## 空阶段，与任意集合处的一步初步函数
<!--/-->

<!--en-->
Two housekeeping facts and one generalization before the reduction. Both towers
are empty at the zero index, so the empty set is a member of every stage whose
index has zero below it. And the absorption of a rud step never used the level
structure of the set it steps over: it holds at any set the constructible stage
already contains, which is the form the reduction consumes.
<!--zh-->
归约之前，两件杂务与一处推广。两塔在零索引处皆空，故空集是每个索引之下有零的阶段的成员。而一步初步函数的吸收从未用到被跨越之集的层结构：它对可构造阶段已经收下的任意集合都成立，而这正是归约所消费的形式。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

empty-⊆ : (u : S) → ((x : S) → ⟨ x ∈ˢ u ⟩ → Empty.⊥) → u ≡ ∅
empty-⊆ u no = ext-⊆ (λ x h → Empty.rec (no x h))
  (λ x h → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h)))

Lset-zero : Lset ∅ ≡ ∅
Lset-zero = empty-⊆ (Lset ∅) (λ x h → PT.rec Empty.isProp⊥
  (λ { (δ , δ∈∅ , _) → ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅) })
  (Lset-out ∅ x h))

Sset-zero : Sset ∅ ≡ ∅
Sset-zero = empty-⊆ (Sset ∅) (λ x h → PT.rec Empty.isProp⊥
  (λ { (δ , δ∈∅ , _) → ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅) })
  (Sset-out ∅ x h))

∅∈Sset : (γ : S) → ⟨ ∅ ∈ˢ γ ⟩ → ⟨ ∅ ∈ˢ Sset γ ⟩
∅∈Sset γ ∅∈γ = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) Sset-zero
  (Sset-mem {α = γ} {β = ∅} ∅∈γ)

∅∈Lset : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ ∅ ∈ˢ γ ⟩ → ⟨ ∅ ∈ˢ Lset γ ⟩
∅∈Lset γ limγ ∅∈γ = Lset-mono {α = γ} {β = sucV ∅}
  (limit-succ-mem γ ∅ limγ ∅∈γ)
  (subst (λ w → ⟨ w ∈ˢ Lset (sucV ∅) ⟩) Lset-zero (Lset∈Lsuc ∅))

ValuesInU : (u ζ : S) → Type (ℓ-suc ℓ)
ValuesInU u ζ = (i : Op16) (a b : S)
  → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u))
  → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩

Lstep⊆ : (u ζ : S) → ⟨ A ∈ˢ Lset ζ ⟩ → ⟨ u ∈ˢ Lset ζ ⟩ → ValuesInU u ζ
       → (x : S) → ⟨ x ∈ˢ step u ⟩ → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
Lstep⊆ u ζ hA u∈L vb x x∈step =
  PT.rec (snd (x ∈ˢ Lset (sucV ζ))) go (step-out u x x∈step)
  where
  up : (y : S) → ⟨ y ∈ˢ Lset ζ ⟩ → ⟨ y ∈ˢ Lset (sucV ζ) ⟩
  up y h = Lset-mono {α = sucV ζ} {β = ζ} (self∈sucV ζ) h
  go : StepArm u x → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
  go (arm-member x∈u) = up x (Ltr ζ {x = u} {y = x} x∈u u∈L)
  go (arm-self x≡u) = up x (subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym x≡u) u∈L)
  go (arm-image i a b sa sb x≡) =
    subst (λ w → ⟨ w ∈ˢ Lset (sucV ζ) ⟩) (sym x≡)
      (Ljunk ζ hA u u∈L i a b sa sb (vb i a b sa sb))
```

<!--en-->
## The reduction

Everything above is assembled here into a single induction along the membership
relation, which discharges the identification of the towers from three named
facts and nothing else. The induction carries three statements at each ordinal
index: the constructible stage is a **member** of every rud level above it, the
two towers agree at the index when it is a limit, and the rud level is included
in and a member of every constructible stage above it. The agreement clause uses
only the induction hypothesis, so the other two may use it at their own index,
and no case analysis on the *shape* of the limit is needed: the ordinal case
split (zero, successor, limit) does all the work, and no ordinal arithmetic
enters.

The three hypotheses are exactly the two facts the recap named plus the
member-characterization reads. `defStage∈J` is one Def stage up staying a rud
member; `stepSet∈L` is one rud step being a *definable set* over a constructible
stage; `values∈L` is the sixteen reads. `slot∈L` places the relativization slot,
and is immediate for the trunk instantiation, where the slot is empty.
<!--zh-->
## 归约

以上一切在此装配成沿成员关系的单场归纳，它把两塔的认同从三条具名事实、别无其他中兑付出来。归纳在每个序数索引处携带三条陈述：可构造阶段是其上每个初步函数层的**成员**；该索引若为极限，两塔在该处相合；以及初步函数层被其上每个可构造阶段包含并成为其成员。相合子句只用归纳假设，故另外两条可以在自己的索引处使用它，而无须对极限的**形状**做情形分析：序数三分 (零、后继、极限) 承担全部工作，序数算术一步也不进场。

三条假设恰是小结所点名的两条事实加上成员刻画的诸次读取。`defStage∈J` 是「上升一个 Def 阶段仍为初步函数成员」；`stepSet∈L` 是「一步初步函数是可构造阶段上的**可定义集**」；`values∈L` 是那十六次读取。`slot∈L` 安放相对化槽，在主干实例化处立得，因为那里的槽是空集。
<!--/-->

```agda
opaque
  -- perf: P-i layer cap: four exposed Lset ∘ sucV layers doubled the check;
  -- the alias keeps at most one layer in conversion position.
  suc⁴ : S → S
  suc⁴ ζ = sucV (sucV (sucV (sucV ζ)))

opaque
  unfolding suc⁴
  suc⁴∈ : (γ ζ : S) → ⟨ isLimit γ ⟩ → ⟨ ζ ∈ˢ γ ⟩ → ⟨ suc⁴ ζ ∈ˢ γ ⟩
  suc⁴∈ γ ζ limγ ζ∈γ = limit-succ-mem γ _ limγ (limit-succ-mem γ _ limγ
    (limit-succ-mem γ _ limγ (limit-succ-mem γ ζ limγ ζ∈γ)))

  suc⁴-up : (ζ y : S) → ⟨ y ∈ˢ Lset ζ ⟩ → ⟨ y ∈ˢ Lset (suc⁴ ζ) ⟩
  suc⁴-up ζ y h = up (sucV (sucV (sucV ζ))) (up (sucV (sucV ζ)) (up (sucV ζ)
    (up ζ h)))
    where
    up : (ξ : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
    up ξ k = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) k
```

<!--en-->
The reduction proper.
<!--zh-->
归约本体。
<!--/-->

```agda
module Reduce
  (defStage∈J : (ζ γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ ζ ∈ˢ γ ⟩
              → ⟨ Lset ζ ∈ˢ Sset γ ⟩ → ⟨ Lset (sucV ζ) ∈ˢ Sset γ ⟩)
  (stepSet∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩
             → ⟨ A ∈ˢ Lset ζ ⟩
             → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
             → ⟨ step u ∈ˢ Lset (sucV ζ) ⟩)
  (values∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩
            → ValuesInU u (suc⁴ ζ))
  (slot∈L : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩)
  where

  RudBelow : S → S → Type (ℓ-suc ℓ)
  RudBelow β γ = ((v : S) → ⟨ v ∈ˢ Sset β ⟩ → ⟨ v ∈ˢ Lset γ ⟩)
               × ⟨ Sset β ∈ˢ Lset γ ⟩

  isPropRudBelow : (β γ : S) → isProp (RudBelow β γ)
  isPropRudBelow β γ = isProp× (isPropΠ2 (λ v _ → snd (v ∈ˢ Lset γ)))
    (snd (Sset β ∈ˢ Lset γ))

  Joint : S → Type (ℓ-suc ℓ)
  Joint β = IsOrd β
    → (((γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ β ∈ˢ γ ⟩ → ⟨ Lset β ∈ˢ Sset γ ⟩)
      × (((limβ : ⟨ isLimit β ⟩) → Lset β ≡ Sset β)
      × ((γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ β ∈ˢ γ ⟩ → RudBelow β γ)))

  jstep : (β : S) → ((β₀ : S) → β₀ ∈ᵗ β → Joint β₀) → Joint β
  jstep β IH ordβ = (p2 , (p3 , p4))
    where
    ihOrd : (β₀ : S) → ⟨ β₀ ∈ˢ β ⟩ → IsOrd β₀
    ihOrd β₀ h = mem-ord {A = β} ordβ β₀ h
    inγ : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ β ∈ˢ γ ⟩ → (δ : S) → ⟨ δ ∈ˢ β ⟩
        → ⟨ δ ∈ˢ γ ⟩
    inγ γ limγ β∈γ δ δ∈β = isLimit-ord γ limγ .fst {x = β} {y = δ} δ∈β β∈γ

    p3 : (limβ : ⟨ isLimit β ⟩) → Lset β ≡ Sset β
    p3 limβ = ext-⊆ sub sup
      where
      sub : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ Sset β ⟩
      sub x x∈ = PT.rec (snd (x ∈ˢ Sset β)) go (Lset-out β x x∈)
        where
        go : Σ[ β₀ ∈ S ] (⟨ β₀ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset β₀) ⟩) → ⟨ x ∈ˢ Sset β ⟩
        go (β₀ , β₀∈β , h) = Ldef→J β₀ β limβ
          (IH β₀ β₀∈β (ihOrd β₀ β₀∈β) .fst β limβ β₀∈β) x h
      sup : (x : S) → ⟨ x ∈ˢ Sset β ⟩ → ⟨ x ∈ˢ Lset β ⟩
      sup x x∈ = PT.rec (snd (x ∈ˢ Lset β)) go (Sset-out β x x∈)
        where
        go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ Lset β ⟩
        go (δ , δ∈β , h) =
          IH (sucV δ) sδ∈β (suc-ord (ihOrd δ δ∈β)) .snd .snd β limβ sδ∈β .fst x
            (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) h)
          where
          sδ∈β : ⟨ sucV δ ∈ˢ β ⟩
          sδ∈β = limit-succ-mem β δ limβ δ∈β

    p2 : (γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ β ∈ˢ γ ⟩ → ⟨ Lset β ∈ˢ Sset γ ⟩
    p2 γ limγ β∈γ = go (ord-case β ordβ)
      where
      go : (β ≡ ∅) ⊎ (⟨ isSucc β ⟩ ⊎ ⟨ isLimit β ⟩) → ⟨ Lset β ∈ˢ Sset γ ⟩
      go (inl z) = subst (λ w → ⟨ Lset w ∈ˢ Sset γ ⟩) (sym z)
        (subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sym Lset-zero)
          (∅∈Sset γ (subst (λ w → ⟨ w ∈ˢ γ ⟩) z β∈γ)))
      go (inr (inl (ζ , ordζ , sζ≡β))) =
        subst (λ w → ⟨ Lset w ∈ˢ Sset γ ⟩) sζ≡β
          (defStage∈J ζ γ limγ ζ∈γ (IH ζ ζ∈β ordζ .fst γ limγ ζ∈γ))
        where
        ζ∈β : ⟨ ζ ∈ˢ β ⟩
        ζ∈β = subst (λ w → ⟨ ζ ∈ˢ w ⟩) sζ≡β (self∈sucV ζ)
        ζ∈γ : ⟨ ζ ∈ˢ γ ⟩
        ζ∈γ = inγ γ limγ β∈γ ζ ζ∈β
      go (inr (inr limβ)) = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sym (p3 limβ))
        (Sset-mem {α = γ} {β = β} β∈γ)

    p4 : (γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ β ∈ˢ γ ⟩ → RudBelow β γ
    p4 γ limγ β∈γ = go (ord-case β ordβ)
      where
      go : (β ≡ ∅) ⊎ (⟨ isSucc β ⟩ ⊎ ⟨ isLimit β ⟩) → RudBelow β γ
      go (inl z) = subst (λ w → RudBelow w γ) (sym z)
        ( (λ v h → Empty.rec (∅-empty v (∈∈ₛ {a = v} {b = ∅} .fst
            (subst (λ w → ⟨ v ∈ˢ w ⟩) Sset-zero h))))
        , subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym Sset-zero)
            (∅∈Lset γ limγ (subst (λ w → ⟨ w ∈ˢ γ ⟩) z β∈γ)) )
      go (inr (inl (δ , ordδ , sδ≡β))) =
        subst (λ w → RudBelow w γ) sδ≡β
          (PT.rec (isPropRudBelow (sucV δ) γ) atStage
            (Lstage₂ γ limγ (Sset δ) A
              (IH δ δ∈β ordδ .snd .snd γ limγ δ∈γ .snd) (slot∈L γ limγ)))
        where
        δ∈β : ⟨ δ ∈ˢ β ⟩
        δ∈β = subst (λ w → ⟨ δ ∈ˢ w ⟩) sδ≡β (self∈sucV δ)
        δ∈γ : ⟨ δ ∈ˢ γ ⟩
        δ∈γ = inγ γ limγ β∈γ δ δ∈β
        atStage : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ γ ⟩ × ⟨ Sset δ ∈ˢ Lset ζ ⟩ × ⟨ A ∈ˢ Lset ζ ⟩)
                → RudBelow (sucV δ) γ
        atStage (ζ , ζ∈γ , u∈ , A∈) = (subFn , memFn)
          where
          ζ₄ ζ₅ ζ₆ : S
          ζ₄ = suc⁴ ζ
          ζ₅ = sucV ζ₄
          ζ₆ = sucV ζ₅
          up₁ : (ξ y : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
          up₁ ξ y h = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) h
          ζ₄∈γ : ⟨ ζ₄ ∈ˢ γ ⟩
          ζ₄∈γ = suc⁴∈ γ ζ limγ ζ∈γ
          ζ₅∈γ : ⟨ ζ₅ ∈ˢ γ ⟩
          ζ₅∈γ = limit-succ-mem γ ζ₄ limγ ζ₄∈γ
          ζ₆∈γ : ⟨ ζ₆ ∈ˢ γ ⟩
          ζ₆∈γ = limit-succ-mem γ ζ₅ limγ ζ₅∈γ
          u∈₄ : ⟨ Sset δ ∈ˢ Lset ζ₄ ⟩
          u∈₄ = suc⁴-up ζ (Sset δ) u∈
          A∈₄ : ⟨ A ∈ˢ Lset ζ₄ ⟩
          A∈₄ = suc⁴-up ζ A A∈
          stepSub : (v : S) → ⟨ v ∈ˢ step (Sset δ) ⟩ → ⟨ v ∈ˢ Lset ζ₅ ⟩
          stepSub = Lstep⊆ (Sset δ) ζ₄ A∈₄ u∈₄ (values∈L (Sset δ) ζ u∈)
          u∈₅ : ⟨ Sset δ ∈ˢ Lset ζ₅ ⟩
          u∈₅ = up₁ ζ₄ (Sset δ) u∈₄
          subFn : (v : S) → ⟨ v ∈ˢ Sset (sucV δ) ⟩ → ⟨ v ∈ˢ Lset γ ⟩
          subFn v h = Lset-mono {α = γ} {β = ζ₅} ζ₅∈γ
            (stepSub v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Sset-suc δ) h))
          memFn : ⟨ Sset (sucV δ) ∈ˢ Lset γ ⟩
          memFn = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (Sset-suc δ))
            (Lset-mono {α = γ} {β = ζ₆} ζ₆∈γ
              (stepSet∈L (Sset δ) ζ₅ u∈₅ (up₁ ζ₄ A A∈₄) stepSub))
      go (inr (inr limβ)) = (subFn , memFn)
        where
        subFn : (v : S) → ⟨ v ∈ˢ Sset β ⟩ → ⟨ v ∈ˢ Lset γ ⟩
        subFn v h = PT.rec (snd (v ∈ˢ Lset γ)) atEnter (Sset-out β v h)
          where
          atEnter : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ v ∈ˢ step (Sset δ) ⟩)
                  → ⟨ v ∈ˢ Lset γ ⟩
          atEnter (δ , δ∈β , hv) =
            IH (sucV δ) sδ∈β (suc-ord (ihOrd δ δ∈β)) .snd .snd γ limγ
              (inγ γ limγ β∈γ (sucV δ) sδ∈β) .fst v
              (subst (λ w → ⟨ v ∈ˢ w ⟩) (sym (Sset-suc δ)) hv)
            where
            sδ∈β : ⟨ sucV δ ∈ˢ β ⟩
            sδ∈β = limit-succ-mem β δ limβ δ∈β
        memFn : ⟨ Sset β ∈ˢ Lset γ ⟩
        memFn = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (p3 limβ)
          (Lset-mono {α = γ} {β = sucV β} (limit-succ-mem γ β limγ β∈γ)
            (Lset∈Lsuc β))

  joint : (β : S) → Joint β
  joint = ∈-induction jstep

  matching : Matching
  matching γ limγ = joint γ (isLimit-ord γ limγ) .snd .fst limγ

  open Bridged matching public
```
