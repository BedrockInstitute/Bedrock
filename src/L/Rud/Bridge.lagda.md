# The bridge between the two towers

<!--en-->
Gödel's definition and Jensen's definition meet here. The constructible tower
takes definable subsets at every stage; the rud tower takes one closure step at
every stage and collects at limits. This chapter connects the two surfaces at
the level of single steps, in both directions, and records exactly what a
per-level identification of the towers costs: the identification is false,
the classical sandwich stands in its place, and the direction from the rud
tower into `L` survives.
<!--zh-->
哥德尔的定义与 Jensen 的定义在此相遇。可构造塔在每个阶段取可定义子集，初步函数塔在每个阶段走一步闭包、在极限处收拢。本章在单步的层面双向连接两个表面，并如实记下逐层认同两塔的代价：认同是假的，经典的三明治取而代之，而自初步函数塔进入 `L` 的那个方向得以保留。
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
open import V.Hierarchy {ℓ} using
  ( 𝒮ᵥ; ∈-irrefl; ∈-induction; ∈-induction-compute; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-in; Lset-out; Lset-mono; Lset-layer; layer-trans
  ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; isL; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Rud.Ops {ℓ} using ( F0; F0-spec; F1; F2; F3; F4; F5; F6; F7 )
open import L.Rud.Images {ℓ} using ( F8; F10; left; right; module F15Of )
open import L.Rud.Describe {ℓ} using
  ( module F0Desc; module F1Desc; module F2Desc; module F3Desc; module F4Desc
  ; module F5Desc; module F6Desc; module F7Desc; module F8Desc
  ; module F10Desc )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( sucIter; sucIter-ord; +ω; +ω-in; +ω-out; +ω-mem; +ω-ord; +ω-limit )
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
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; setUnion-ord )
open import L.Rud.ClassJ {ℓ} lem A using ( isJ; Jset→isJ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.Switch {ℓ} lem A using ( module Descr; module Hops )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; ⋃_; union-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
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

The two towers are identified where both are read at the same limit index. The
identification was recorded in this chapter as the statement
`Matching`{.Agda}, the one hypothesis the chapter would not prove. It is not
merely unproved: it is **false**. Devlin's *Constructibility*, VI.2.4, names
the general equality `J_α = L_{ω·α}` as the tempting error and refutes it;
equality holds exactly at the ω-fixed points. The failure is visible at the
second block. At `ζ = ω`, `γ = ω·2`, the level `L_ω` is a member of
`S_{ω·2}`: `L_ω = S_ω`, and `S_ω ∈ step (S_ω) ⊆ S_{ω·2}`. Yet no limit stage
below `ω·2` holds `L_ω`: the only limit below is `ω`, and a stage never holds
itself. The classical refutation is the arithmetic truth set: the codes
`T ⊆ ω` of the sentences true in `(L_ω , ∈)` lie in `L_{ω+2}` but not in
`S_{ω·2}`, since `S_{ω·2} ∩ 𝒫(L_ω) = Def(L_ω)` and Tarski's theorem says a
structure's full satisfaction relation is not definable over it. So
`Matching` at `γ = ω·2` would assert `L_{ω·2} = S_{ω·2}`, which is false.

What is true, classically, is the sandwich of VI.2.4(i): for every ordinal
`α`, `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)`, with equality on both sides exactly
at the ω-fixed points, `ω·α = α`. The sandwich is recorded here as a
classical fact in prose: it is neither proved in this chapter nor assumed as a
postulate.

The deliverable is therefore the direction that needs no identification. A
member of a rud level is a member of a constructible stage:
`bridge-isJ→isL`{.Agda} is proved inside the reshaped reduction, read off the
surviving half of Devlin's `P(α)` (for `β ∈ γ` at a limit `γ`, the rud level
`Sset β` is included in `Lset γ`), re-proved without the per-level
identification. The reverse class direction is delivered at the tower:
`bridge-isL→isJ`{.Agda} lands each `L`-member in the rud level the reshaped
induction `Q` supplies. The module `Bridged`{.Agda}, which packaged both
directions over the false hypothesis, is retired.
<!--zh-->
## 桥

两塔在同一极限索引处被同时读出之处认同。认同在本章中记作陈述 `Matching`{.Agda}，即本章唯一不证的那条假设。它不只是未证：它是**假的**。Devlin 的 *Constructibility* VI.2.4 把一般等式 `J_α = L_{ω·α}` 点名为诱人的错误并加以驳斥；等式恰好在 ω 不动点处成立。失败在第二个块就看得见。在 `ζ = ω`、`γ = ω·2` 处，层 `L_ω` 是 `S_{ω·2}` 的成员：`L_ω = S_ω`，且 `S_ω ∈ step (S_ω) ⊆ S_{ω·2}`。然而 `ω·2` 之下没有任何极限阶段持有 `L_ω`：其下唯一的极限是 `ω`，而阶段从不持有自身。经典的驳斥是算术真值集：在 `(L_ω , ∈)` 中为真的诸句子的码集 `T ⊆ ω` 落在 `L_{ω+2}` 里，却不在 `S_{ω·2}` 里，因为 `S_{ω·2} ∩ 𝒫(L_ω) = Def(L_ω)`，而 Tarski 定理说一个结构的完全满足关系不在它自身之上可定义。故 `Matching` 在 `γ = ω·2` 处会断言 `L_{ω·2} = S_{ω·2}`，那是假的。

经典地为真的是 VI.2.4 (i) 的三明治：对每个序数 `α`，有 `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)`，两侧等号恰在 ω 不动点 `ω·α = α` 处成立。三明治在此作为经典事实记于文稿：本章不证明它，也绝不把它立为公设。

交付物因而是完全不需要认同的那个方向。初步函数层的成员就是可构造阶段的成员：`bridge-isJ→isL`{.Agda} 在重塑后的归约内部，从 Devlin 的 `P(α)` 的存活半边 (在极限 `γ` 处、`β ∈ γ` 时，初步函数层 `Sset β` 被 `Lset γ` 包含) 读出，且不倚靠分层认同。反方向的类陈述如今在塔处交付：`bridge-isL→isJ`{.Agda} 把每个 `L` 成员落进重塑后的归纳 `Q` 供应的初步函数层。曾把两个方向打包在假假设之上的模块 `Bridged`{.Agda} 已经退休。
<!--/-->

```agda
Matching : Type (ℓ-suc ℓ)
Matching = (γ : S) → (limγ : ⟨ isLimit γ ⟩) → Lset γ ≡ Jset γ limγ
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
inside a limit. The lemma below takes the equality of the two towers at a limit
index as a hypothesis and supplies the membership hypothesis at the successor
of that index; the whole absorption then sits two stages above such an index,
three for the pair-valued values, and all of it is absorbed by the next limit
stage.
<!--zh-->
吸收如何被消费，看这里，而它所索取的比预想的更少：不需要两塔的认同，只需要某个可构造阶段把初步函数层作为**成员**收下。那么该层之上一步初步函数便可逐臂对着下一个阶段读出：层的成员由传递性成为阶段的成员，层自身径直就是成员，而每个像值由吸收而可定义。这一步仍要索取的是子集一侧，即每个值的诸成员早已在该阶段之内；此处取作假设，因为清偿它意味着把十六个运算的成员刻画各读一遍。对值的那几个比平坦的那几个多花一个阶段，因为它们的成员是对，而配对只在极限内部封闭。下方的引理把两塔在某极限索引处的等式取作假设，在该索引的后继处供应那条隶属假设；整场吸收于是坐在这样的极限之上两个阶段，对值者三个，而这一切都被下一个极限阶段吸收。
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
member. The verified offset is therefore **two** stages above a limit index at
which the equality of the two towers is assumed: one to hold the level, one to
define the value. Pairing is closed inside a limit stage, which is the subset
condition for the pair-valued operations.

What is not delivered here is the identification of the two towers at limit
indices, and the reason is worth recording: the identification is **false**
(Devlin VI.2.4; the bridge section records the counter-instance at `ζ = ω`,
`γ = ω·2`), not merely unproved. Both directions of an interleaving ask for
the levels of one tower to be **members** of the other's, and each of those is
a definability statement about a hierarchy rather than about a single step: on
one side the rud step operator would have to be definable over a constructible
stage (which needs the graphs of the sixteen operations, not their values), on
the other the constructible stages would have to appear inside the rud tower.
The class equivalence is packaged at the tower: `bridge-isL→isJ`{.Agda} is
delivered from the reshaped induction `Q`, and
`bridge-isJ→isL`{.Agda} is read off the surviving half of Devlin's `P(α)`,
re-proved without the per-level identification, with the limit membership of
that half carried as the named residue `below-lim` beside the induction's own
limit residue `Q-lim`. The module that carried both directions over the false
hypothesis is retired, and the true relationship between the levels, the
classical sandwich `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)` of VI.2.4(i), is
recorded as a fact in prose at the bridge.
<!--zh-->
两个单步都已造出。可构造阶段的一个可定义子集，只要该阶段是初步函数塔某极限层的**成员**，就落进那个极限层，这是把满足集引擎读在一个自身并非层的载体上。反方向，十六个运算在任意传递载体上都有描述，故载体既收下实参又收下诸成员的那个值在其上可定义；而一步初步函数的垃圾，即实参槽里坐着层自身的那些值，一旦某个阶段把该层作为成员收下便成了寻常之物。故经核实的偏移是两塔等式被假设处的极限索引之上**两**个阶段：一个用来收下层，一个用来定义值。配对在极限阶段内部封闭，这正是对值运算所需的子集条件。

此处不交付的是两塔在极限索引处的认同，而其缘由值得记下：认同是**假的** (Devlin VI.2.4，桥一节记下了 `ζ = ω`、`γ = ω·2` 处的反例)，并非仅仅未证。交错的两个方向都要求一塔的诸层是另一塔的**成员**，而这两件事都是关于层级而非关于单步的可定义性陈述：一侧要求初步函数的 step 算子在可构造阶段上可定义 (那需要十六运算的图，而非它们的值)，另一侧要求可构造诸阶段出现在初步函数塔之内。类的等价如今在塔处打包：`bridge-isL→isJ`{.Agda} 由重塑后的归纳 `Q` 交付，`bridge-isJ→isL`{.Agda} 从 Devlin 的 `P(α)` 的存活半边读出、在分层认同之外重证，其极限成员隶属与归纳自己的极限残项 `Q-lim` 一并作为具名残项 `below-lim` 携带。曾把等价打包在假假设之上的模块已经退休；诸层之间的真实关系，即 VI.2.4 (i) 的经典三明治 `Lset α ⊆ Sset (ω·α) ⊆ Lset (ω·α)`，作为事实记于桥一节的文稿。
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
## The index tower

Everything above is assembled here into a reshaped reduction, and the
reduction's index arithmetic is now a tower of its own. The old induction
carried the arithmetic by hand: the membership clause ran over every limit
above the index and collapsed the first limit, and no ordinal arithmetic
entered. The replacement tower is the closed form the classical index needs:
`γ β = +ω (⋃_{δ<β} γ δ)`, Devlin's `γ(β) = ω·(β+1)`, one recursion covering
zero (the union over the empty index is empty, so `γ ∅ = +ω ∅ = ω`),
successors (the running sup collapses to `γ β`, so `γ (sucV β) = +ω (γ β)`,
the next ω-block) and limits (the brief's `γ(λ) := +ω (⋃_{β<λ} γ β)`
verbatim). The tower is sealed opaque at birth with `γ-compute` as its only
unfolding, and it carries the two facts the reshaped induction needs of it:
every value is a limit, unconditionally (`γ-lim`), and the successor step is
the ω-block (`γ-suc`).

The tower is monotone in its index, and the monotonicity is the one wall this
design fires. The step operator `sucV` is not subset-monotone: `sucV u =
u ∪ {u}` needs `u ∈ v`, which `u ⊆ v` never gives (D-8). The conditioned kit
is the native shape, not a patch: the step is monotone under `u ⊆ v` together
with `u ∈ v`, the trichotomy of ordinals supplies the membership at each
finite iterate, and both the tower's monotonicity and its successor equation
run on it.
<!--zh-->
## 索引塔

以上一切在此装配成重塑后的归约，而归约的索引算术如今自成一座塔。旧归纳亲手搬运这段算术：成员子句跑过索引之上的每个极限、并在第一个极限处坍缩，序数算术一步也不进场。替换它的塔正是经典索引所需的闭式：`γ β = +ω (⋃_{δ<β} γ δ)`，即 Devlin 的 `γ(β) = ω·(β+1)`，一场递归同时覆盖零 (空索引上的并是空的，故 `γ ∅ = +ω ∅ = ω`)、后继 (运行中的上确界坍缩为 `γ β`，故 `γ (sucV β) = +ω (γ β)`，即下一个 ω 块) 与极限 (`γ(λ) := +ω (⋃_{β<λ} γ β)` 原样照抄)。塔一出生即不透明封印，`γ-compute` 是它唯一的展开，而它携带重塑后的归纳所需的两个事实：每个值都是极限，无条件成立 (`γ-lim`)；后继步就是 ω 块 (`γ-suc`)。

塔在索引上单调，而这条单调性正是本设计打出的那面墙。step 算子 `sucV` 不在子集序上单调：`sucV u = u ∪ {u}` 需要 `u ∈ v`，而 `u ⊆ v` 永远给不出这一点 (D-8)。带条件的套件是原生形状，不是补丁：step 在 `u ⊆ v` 连同 `u ∈ v` 下单调，序数三歧在每个有限迭代处供给隶属，塔的单调性与后继方程都跑在它上面。
<!--/-->

```agda
-- The tower's own index arithmetic, closed form (the probe's measured shape).
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

towerStep : (α : S) → (∀ δ → δ ∈ᵗ α → S) → S
towerStep α rec = +ω (⋃ (sett ⟪ α ⟫ (λ m → rec (⟪ α ⟫↪ m) (mem m))))
  where
  mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
  mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

opaque
  γ : S → S
  γ = ∈-induction towerStep

opaque
  unfolding γ
  γ-compute : (α : S) → γ α ≡ towerStep α (λ δ _ → γ δ)
  γ-compute = ∈-induction-compute towerStep

-- The tower read as a family, and its bound union (the union term is bound,
-- C-20: no inline `∈ˢ ⋃`).
fam : (α : S) → ⟪ α ⟫ → S
fam α m = γ (⟪ α ⟫↪ m)

U : S → S
U α = ⋃ (sett ⟪ α ⟫ (fam α))

-- The base: the union over the empty index is empty, so γ ∅ = +ω ∅ = ω.
U-zero : U ∅ ≡ ∅
U-zero = ext-⊆ (λ x x∈ → Empty.rec {A = ⟨ x ∈ˢ ∅ ⟩}
  (PT.rec Empty.isProp⊥ (go x)
    (union-ax (sett ⟪ ∅ ⟫ (fam ∅)) x .fst (∈∈ₛ {a = x} {b = U ∅} .fst x∈))))
  (λ x x∈∅ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅)))
  where
  go : (x : S) → Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ ∅ ⟫ (fam ∅) ⟩ × ⟨ x ∈ₛ v ⟩)
     → Empty.⊥
  go x (v , v∈ , _) = PT.rec Empty.isProp⊥ atFib
    (∈∈ₛ {a = v} {b = sett ⟪ ∅ ⟫ (fam ∅)} .snd v∈)
    where
    atFib : Σ[ m ∈ ⟪ ∅ ⟫ ] (fam ∅ m ≡ v) → Empty.⊥
    atFib (m , _) = ∅-empty (⟪ ∅ ⟫↪ m) (∈ₛ⟪ ∅ ⟫↪ m)

-- The tower is ordinal-valued, unconditionally: every value is +ω of the
-- running sup, and the sup is an ordinal over ordinal family members.
γ-ord : (α : S) → IsOrd (γ α)
γ-ord = ∈-induction ordStep
  where
  ordStep : (α : S) → (∀ δ → δ ∈ᵗ α → IsOrd (γ δ)) → IsOrd (γ α)
  ordStep α IH = subst IsOrd (sym (γ-compute α))
    (+ω-ord (U α) (setUnion-ord ⟪ α ⟫ (fam α) hfam))
    where
    mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
    mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
    hfam : (m : ⟪ α ⟫) → IsOrd (fam α m)
    hfam m = IH (⟪ α ⟫↪ m) (mem m)

ordU : (β : S) → IsOrd (U β)
ordU β = setUnion-ord ⟪ β ⟫ (fam β) (λ m → γ-ord (⟪ β ⟫↪ m))

-- Fact one: every value of the tower is a limit, unconditionally.  This is
-- what makes Sset (γ β) a J-level, so BlockPowLim and the full switch apply
-- at the tower's own index.
γ-lim : (α : S) → ⟨ isLimit (γ α) ⟩
γ-lim α = subst (λ w → ⟨ isLimit w ⟩) (sym (γ-compute α))
  (+ω-limit (U α) (ordU α))

-- The monotonicity kit (D-8's conditioned form): the step operator is not
-- subset-monotone, so the block map is monotone only at ordinal arguments,
-- where the trichotomy supplies the membership.
sucV-mono-cond : {u v : S} → u ⊆ v → ⟨ u ∈ˢ v ⟩ → sucV u ⊆ sucV v
sucV-mono-cond {u} {v} sub u∈v x x∈ = ∈sucV-elim (snd (x ∈ˢ sucV v)) x∈
  (λ x∈u → ∈sucV-inl (sub x x∈u))
  (λ x≡u → ∈sucV-inl (subst (λ w → ⟨ w ∈ˢ v ⟩) (sym x≡u) u∈v))

sucIter-mono-ord : (u v : S) → IsOrd u → IsOrd v → u ⊆ v → (n : ℕ)
                 → sucIter n u ⊆ sucIter n v
sucIter-mono-ord u v ou ov sub zero x x∈ = sub x x∈
sucIter-mono-ord u v ou ov sub (suc n) x x∈ =
  go (sucIter-ord n ou) (sucIter-ord n ov)
     (ord-tri (sucIter n u) (sucIter-ord n ou) (sucIter n v) (sucIter-ord n ov))
     x x∈
  where
  go : IsOrd (sucIter n u) → IsOrd (sucIter n v)
     → Tri (sucIter n u) (sucIter n v)
     → (x : S) → ⟨ x ∈ˢ sucV (sucIter n u) ⟩ → ⟨ x ∈ˢ sucV (sucIter n v) ⟩
  go ou' ov' (inl u∈v) x x∈ =
    sucV-mono-cond (sucIter-mono-ord u v ou ov sub n) u∈v x x∈
  go ou' ov' (inr (inl e)) x x∈ =
    subst (λ w → ⟨ x ∈ˢ w ⟩) (cong sucV e) x∈
  go ou' ov' (inr (inr v∈u)) x x∈ = Empty.rec (∈-irrefl (sucIter n v)
    (sucIter-mono-ord u v ou ov sub n (sucIter n v) v∈u))

+ω-mono-ord : (u v : S) → IsOrd u → IsOrd v → u ⊆ v → +ω u ⊆ +ω v
+ω-mono-ord u v ou ov sub x x∈ = PT.rec (snd (x ∈ˢ +ω v)) go (+ω-out u x x∈)
  where
  go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω v ⟩
  go (n , x∈n) = +ω-in v x n (sucIter-mono-ord u v ou ov sub (suc n) x x∈n)

-- The tower is monotone in the index: δ ∈ α gives γ δ ⊆ γ α.
γ-mono : (α δ : S) → IsOrd α → ⟨ δ ∈ˢ α ⟩ → γ δ ⊆ γ α
γ-mono α δ ordα δ∈α x x∈γδ =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (γ-compute α))
    (+ω-mono-ord (U δ) (U α) (ordU δ) (ordU α) (Uδ⊆Uα) x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (γ-compute δ) x∈γδ))
  where
  Uδ⊆Uα : U δ ⊆ U α
  Uδ⊆Uα y y∈Uδ = PT.rec (snd (y ∈ˢ U α)) atFib0
    (union-ax (sett ⟪ δ ⟫ (fam δ)) y .fst (∈∈ₛ {a = y} {b = U δ} .fst y∈Uδ))
    where
    atFib0 : Σ[ w ∈ S ] (⟨ w ∈ₛ sett ⟪ δ ⟫ (fam δ) ⟩ × ⟨ y ∈ₛ w ⟩)
           → ⟨ y ∈ˢ U α ⟩
    atFib0 (w , w∈ , y∈w) = PT.rec (snd (y ∈ˢ U α)) atFib
      (∈∈ₛ {a = w} {b = sett ⟪ δ ⟫ (fam δ)} .snd w∈)
      where
      atFib : Σ[ m ∈ ⟪ δ ⟫ ] (fam δ m ≡ w) → ⟨ y ∈ˢ U α ⟩
      atFib (m , mw) = ∈∈ₛ {a = y} {b = U α} .snd
        (union-ax (sett ⟪ α ⟫ (fam α)) y .snd
          ∣ γ ε , (memb , y∈ₛ) ∣₁)
        where
        ε : S
        ε = ⟪ δ ⟫↪ m
        ε∈δ : ⟨ ε ∈ˢ δ ⟩
        ε∈δ = ∈∈ₛ {a = ε} {b = δ} .snd (∈ₛ⟪ δ ⟫↪ m)
        ε∈α : ⟨ ε ∈ˢ α ⟩
        ε∈α = ordα .fst {x = δ} {y = ε} ε∈δ δ∈α
        fib = ∈-asFiber {a = ε} {b = α} ε∈α
        memb : ⟨ γ ε ∈ₛ sett ⟪ α ⟫ (fam α) ⟩
        memb = ∈∈ₛ {a = γ ε} {b = sett ⟪ α ⟫ (fam α)} .fst
          ∣ fib .fst , cong γ (fib .snd) ∣₁
        y∈ₛ : ⟨ y ∈ₛ γ ε ⟩
        y∈ₛ = subst (λ w → ⟨ y ∈ₛ w ⟩) (sym mw) y∈w

-- Fact two: the successor step of the tower IS the ω-block, γ (sucV β) =
-- +ω (γ β).  The union over sucV β collapses to γ β: below by γ-mono, at
-- the top by the union's own family membership.
γ-suc : (β : S) → IsOrd β → γ (sucV β) ≡ +ω (γ β)
γ-suc β ordβ = ext-⊆ sub sup
  where
  U-suc⊆ : (β : S) → IsOrd β → U (sucV β) ⊆ γ β
  U-suc⊆ β ordβ x x∈U = PT.rec (snd (x ∈ˢ γ β)) atFib0
    (union-ax (sett ⟪ sucV β ⟫ (fam (sucV β))) x .fst
      (∈∈ₛ {a = x} {b = U (sucV β)} .fst x∈U))
    where
    atFib0 : Σ[ w ∈ S ] (⟨ w ∈ₛ sett ⟪ sucV β ⟫ (fam (sucV β)) ⟩ × ⟨ x ∈ₛ w ⟩)
           → ⟨ x ∈ˢ γ β ⟩
    atFib0 (w , w∈ , x∈w) = PT.rec (snd (x ∈ˢ γ β)) atFib
      (∈∈ₛ {a = w} {b = sett ⟪ sucV β ⟫ (fam (sucV β))} .snd w∈)
      where
      atFib : Σ[ m ∈ ⟪ sucV β ⟫ ] (fam (sucV β) m ≡ w) → ⟨ x ∈ˢ γ β ⟩
      atFib (m , mw) = ∈sucV-elim (snd (x ∈ˢ γ β)) δ∈sucβ
        (λ δ∈β → γ-mono β δ ordβ δ∈β x x∈γδ)
        (λ δ≡β → subst (λ t → ⟨ x ∈ˢ γ t ⟩) δ≡β x∈γδ)
        where
        δ : S
        δ = ⟪ sucV β ⟫↪ m
        δ∈sucβ : ⟨ δ ∈ˢ sucV β ⟩
        δ∈sucβ = ∈∈ₛ {a = δ} {b = sucV β} .snd (∈ₛ⟪ sucV β ⟫↪ m)
        x∈γδ : ⟨ x ∈ˢ γ δ ⟩
        x∈γδ = subst (λ t → ⟨ x ∈ˢ t ⟩) (sym mw)
          (∈∈ₛ {a = x} {b = w} .snd x∈w)
  γβ⊆U-suc : (β : S) → γ β ⊆ U (sucV β)
  γβ⊆U-suc β x x∈γβ = ∈∈ₛ {a = x} {b = U (sucV β)} .snd
    (union-ax (sett ⟪ sucV β ⟫ (fam (sucV β))) x .snd
      ∣ γ β , (memb , x∈ₛ) ∣₁)
    where
    fib = ∈-asFiber {a = β} {b = sucV β} (self∈sucV β)
    memb : ⟨ γ β ∈ₛ sett ⟪ sucV β ⟫ (fam (sucV β)) ⟩
    memb = ∈∈ₛ {a = γ β} {b = sett ⟪ sucV β ⟫ (fam (sucV β))} .fst
      ∣ fib .fst , cong γ (fib .snd) ∣₁
    x∈ₛ : ⟨ x ∈ₛ γ β ⟩
    x∈ₛ = ∈∈ₛ {a = x} {b = γ β} .fst x∈γβ
  sub : γ (sucV β) ⊆ +ω (γ β)
  sub x x∈ = +ω-mono-ord (U (sucV β)) (γ β) (ordU (sucV β)) (γ-ord β)
    (U-suc⊆ β ordβ) x
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (γ-compute (sucV β)) x∈)
  sup : +ω (γ β) ⊆ γ (sucV β)
  sup x x∈ = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (γ-compute (sucV β)))
    (+ω-mono-ord (γ β) (U (sucV β)) (γ-ord β) (ordU (sucV β))
      (γβ⊆U-suc β) x x∈)
```

<!--en-->
## The reshaped reduction

The reduction itself is now one statement at the tower's own index. The old
induction carried three clauses at each index, and the middle one, the
agreement of the two towers at a limit, is the per-level identification this
campaign proved false; no clause of the reshaped reduction claims
`Matching`{.Agda}. The induction proves `Q β`, that the constructible stage
`Lset β` is a **member** of the rud level `Sset (γ β)` at the tower's index,
Devlin VI.2.3's `L_α ∈ J_{α+1}` read at the closed form. The zero clause is
the base, `Lset ∅ = Sset ∅ = ∅` and `∅ ∈ γ ∅ = +ω ∅`. The successor clause
is the six-line composition T23 measured: `BlockPowLim` (P1's corrected
target, which SatTable's re-stated relation discharges) lands `𝒟ₒ (Lset β)`
one ω-block up at the limit index `δ = γ β`; `Lset-suc` identifies
`Lset (sucV β)` with `𝒟ₒ (Lset β)`; and `γ-suc` identifies `+ω (γ β)` with
the tower's next value. The limit clause is the expensive one, stated here
and left as the first named residue: at a limit `l`, the tower hypothesis
supplies `Lset δ ∈ Sset (γ δ)` for every `δ ∈ l`, and the clause concludes
`Lset l ∈ Sset (γ l)`. Its proof needs the initial-segment face at the rud
carrier `Sset (⋃_{δ<l} γ δ)` (the level-sigma chapter), the full switch
`full-switch-⊇` one ω-block up, a sup-is-a-limit fact for that carrier, and
`Lset`'s own union structure.

The surviving half of the old reduction is re-proved without the
identification. Devlin's `P(α)` says the rud level `Sset β` is included in,
and a member of, every constructible stage above it, and
`bridge-isJ→isL`{.Agda} is read off the inclusion half. The old proof of the
membership at a limit index leaned on the per-level identification, which is
gone; its identification-free form needs the S-hierarchy's sequence as a
member of the right constructible stage, the same definability family as the
limit clause's residue. The induction below therefore proves the inclusion
and the successor memberships from the three named hypotheses, and carries
the limit membership as the second named residue (`below-lim`). The reverse
class direction is delivered too: `bridge-isL→isJ`{.Agda} lands an
`L`-member through `Lset-out` and `Ldef→J` at the level `Q` supplies,
`Sset (γ δ)`.

The hypotheses are the named facts the recaps recorded. `stepSet∈L` is one
rud step being a *definable set* over a constructible stage; `values∈L` is
the sixteen reads; `slot∈L` places the relativization slot, immediate for the
trunk instantiation where the slot is empty. `blockPowLim` is the successor
step's supply, and the two residues, `Q-lim` and `below-lim`, are the
sequence facts the last funding round must close.
<!--zh-->
## 重塑后的归约

归约本身现在是塔自己索引处的一条陈述。旧归纳在每个索引处携带三条子句，中间那条，即两塔在某极限处的相合，正是本战役证明为假的分层认同；重塑后的归约没有任何子句声称 `Matching`{.Agda}。归纳证明 `Q β`：可构造阶段 `Lset β` 是塔索引处初步函数层 `Sset (γ β)` 的**成员**，即 Devlin VI.2.3 的 `L_α ∈ J_{α+1}` 在闭式上的读法。零子句是基底，`Lset ∅ = Sset ∅ = ∅` 且 `∅ ∈ γ ∅ = +ω ∅`。后继子句是 T23 测过的六行复合：`BlockPowLim` (P1 的修正目标，由 SatTable 重述后的关系兑付) 在极限索引 `δ = γ β` 处把 `𝒟ₒ (Lset β)` 送到一个 ω 块之上；`Lset-suc` 把 `Lset (sucV β)` 认同为 `𝒟ₒ (Lset β)`；`γ-suc` 把 `+ω (γ β)` 认同为塔的下一个值。极限子句是昂贵的那条，此处陈述并留下，作为第一个具名残项：在极限 `l` 处，塔假设为每个 `δ ∈ l` 供应 `Lset δ ∈ Sset (γ δ)`，子句要推出 `Lset l ∈ Sset (γ l)`。它的证明需要 rud 载体 `Sset (⋃_{δ<l} γ δ)` 处的初始段面孔 (层 sigma 章)、高一个 ω 块处的完全切换 `full-switch-⊇`、该载体的「上确界是极限」事实，以及 `Lset` 自身的并结构。

旧归约的存活半边在认同之外重证。Devlin 的 `P(α)` 说初步函数层 `Sset β` 被其上每个可构造阶段包含并成为其成员，`bridge-isJ→isL`{.Agda} 从包含那一半读出。旧证在极限索引处的成员隶属倚靠分层认同，而它已经不在；其免认同形式需要 S 塔的序列作为正确可构造阶段的成员，与极限子句的残项同属一个可定义性家族。故下面的归纳用三条具名假设证包含与后继成员隶属，把极限成员隶属作为第二个具名残项 (`below-lim`) 携带。反方向的类陈述如今也交付：`bridge-isL→isJ`{.Agda} 经 `Lset-out` 与 `Ldef→J`，把 `L` 成员落进 `Q` 供应的层 `Sset (γ δ)`。

假设正是两处小结记下的具名事实。`stepSet∈L` 是「一步初步函数是可构造阶段上的**可定义集**」；`values∈L` 是那十六次读取；`slot∈L` 安放相对化槽，在主干实例化处立得，因为那里的槽是空集。`blockPowLim` 是后继步的供应，两个残项 `Q-lim` 与 `below-lim` 则是最后一段资金要闭合的序列事实。
<!--/-->

```agda
-- The successor step's supply, the P2 residue re-stated by SatTable's
-- chapter (the same type expression, so the landing's discharge is
-- definitionally usable here).
BlockPowLim : Type (ℓ-suc ℓ)
BlockPowLim = (ζ δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
            → ⟨ Lset ζ ∈ˢ Sset δ ⟩ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ) ⟩

-- The reshaped induction's limit clause, stated and left: at a limit l, from
-- the tower hypothesis that every stage below is a member at its own index,
-- conclude that Lset l is a member at γ l.
Q-lim-statement : Type (ℓ-suc ℓ)
Q-lim-statement = (l : S) → IsOrd l → ⟨ isLimit l ⟩
  → ((δ : S) → ⟨ δ ∈ˢ l ⟩ → ⟨ Lset δ ∈ˢ Sset (γ δ) ⟩)
  → ⟨ Lset l ∈ˢ Sset (γ l) ⟩

-- The surviving half's residue: the rud level at a limit index as a member of
-- the constructible stage above it.  The old proof leaned on the per-level
-- identification here; the identification-free form needs the S-sequence in
-- the right constructible stage, the same definability family as Q-lim.
BelowLim : Type (ℓ-suc ℓ)
BelowLim = (γ : S) → (limγ : ⟨ isLimit γ ⟩) → (β : S) → IsOrd β
         → ⟨ isLimit β ⟩ → ⟨ β ∈ˢ γ ⟩ → ⟨ Sset β ∈ˢ Lset γ ⟩

-- The base of the reshaped induction: Lset ∅ = Sset ∅ = ∅, and the first
-- ω-block holds the empty set.
∅∈γ∅ : ⟨ ∅ ∈ˢ γ ∅ ⟩
∅∈γ∅ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (γ-compute ∅))
  (subst (λ w → ⟨ ∅ ∈ˢ +ω w ⟩) (sym U-zero) (+ω-mem ∅))

Q-zero : ⟨ Lset ∅ ∈ˢ Sset (γ ∅) ⟩
Q-zero = subst (λ w → ⟨ w ∈ˢ Sset (γ ∅) ⟩) (sym Lset-zero)
  (subst (λ w → ⟨ w ∈ˢ Sset (γ ∅) ⟩) Sset-zero
    (Sset-mem {α = γ ∅} {β = ∅} ∅∈γ∅))
```

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
The reshaped reduction proper.
<!--zh-->
重塑后的归约本体。
<!--/-->

```agda
module Reduce
  (stepSet∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩
             → ⟨ A ∈ˢ Lset ζ ⟩
             → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
             → ⟨ step u ∈ˢ Lset (sucV ζ) ⟩)
  (values∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩
            → ValuesInU u (suc⁴ ζ))
  (slot∈L : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩)
  (blockPowLim : BlockPowLim)
  (Q-lim : Q-lim-statement)
  (below-lim : BelowLim)
  where

  -- The reshaped induction's successor clause, the six-line composition T23
  -- measured end to end: BlockPowLim at the limit index δ = γ β, Lset-suc,
  -- and γ-suc.  Nothing else enters.
  Q-suc : (β : S) → IsOrd β → ⟨ Lset β ∈ˢ Sset (γ β) ⟩
        → ⟨ Lset (sucV β) ∈ˢ Sset (γ (sucV β)) ⟩
  Q-suc β ordβ L∈ =
    subst (λ w → ⟨ Lset (sucV β) ∈ˢ Sset w ⟩) (sym (γ-suc β ordβ))
      (subst (λ w → ⟨ w ∈ˢ Sset (+ω (γ β)) ⟩) (sym (Lset-suc β))
        (blockPowLim β (γ β) (isLimit-ord (γ β) (γ-lim β)) (γ-lim β) L∈))

  -- The reshaped induction: zero via Q-zero, successor via Q-suc at the
  -- predecessor, limit via the stated residue, endpoint Q = ∈-induction.
  qstep : (β : S) → ((β₀ : S) → β₀ ∈ᵗ β → IsOrd β₀ → ⟨ Lset β₀ ∈ˢ Sset (γ β₀) ⟩)
        → IsOrd β → ⟨ Lset β ∈ˢ Sset (γ β) ⟩
  qstep β IH ordβ = go (ord-case β ordβ)
    where
    go : (β ≡ ∅) ⊎ (⟨ isSucc β ⟩ ⊎ ⟨ isLimit β ⟩) → ⟨ Lset β ∈ˢ Sset (γ β) ⟩
    go (inl z) = subst (λ w → ⟨ Lset w ∈ˢ Sset (γ w) ⟩) (sym z) Q-zero
    go (inr (inl (δ , ordδ , sδ≡β))) =
      subst (λ w → ⟨ Lset w ∈ˢ Sset (γ w) ⟩) sδ≡β
        (Q-suc δ ordδ
          (IH δ (subst (λ w → ⟨ δ ∈ˢ w ⟩) sδ≡β (self∈sucV δ)) ordδ))
    go (inr (inr limβ)) = Q-lim β ordβ limβ
      (λ δ (δ∈β : ⟨ δ ∈ˢ β ⟩) → IH δ δ∈β (mem-ord {A = β} ordβ δ δ∈β))

  Q : (β : S) → IsOrd β → ⟨ Lset β ∈ˢ Sset (γ β) ⟩
  Q = ∈-induction qstep

  -- The class-level L into J direction, delivered at the tower: an L-member
  -- lies in some 𝒟ₒ (Lset δ), and Q supplies the rud level Sset (γ δ) that
  -- Ldef→J then receives it into.
  bridge-isL→isJ : (x : S) → ⟨ isL x ⟩ → ⟨ isJ x ⟩
  bridge-isL→isJ x = PT.rec (snd (isJ x)) go
    where
    go : Σ[ β ∈ S ] (IsOrd β × ⟨ x ∈ˢ Lset β ⟩) → ⟨ isJ x ⟩
    go (β , ordβ , x∈L) = PT.rec (snd (isJ x)) atEnter (Lset-out β x x∈L)
      where
      atEnter : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ isJ x ⟩
      atEnter (δ , δ∈β , h) =
        Jset→isJ (γ δ) (γ-lim δ) x
          (Ldef→J δ (γ δ) (γ-lim δ) (Q δ (mem-ord {A = β} ordβ δ δ∈β)) x h)

  -- The surviving half, Devlin's P(α): for β ∈ γ at a limit γ, the rud level
  -- Sset β is included in Lset γ and is a member of it.  The limit membership
  -- is the second named residue (below-lim); the identification-free proof of
  -- it is the S-sequence definability, the same family as Q-lim.
  RudBelow : S → S → Type (ℓ-suc ℓ)
  RudBelow β γ = ((v : S) → ⟨ v ∈ˢ Sset β ⟩ → ⟨ v ∈ˢ Lset γ ⟩)
               × ⟨ Sset β ∈ˢ Lset γ ⟩

  isPropRudBelow : (β γ : S) → isProp (RudBelow β γ)
  isPropRudBelow β γ = isProp× (isPropΠ2 (λ v _ → snd (v ∈ˢ Lset γ)))
    (snd (Sset β ∈ˢ Lset γ))

  module Below (γ : S) (limγ : ⟨ isLimit γ ⟩) where

    R : S → Type (ℓ-suc ℓ)
    R β = IsOrd β → ⟨ β ∈ˢ γ ⟩ → RudBelow β γ

    rstep : (β : S) → ((β₀ : S) → β₀ ∈ᵗ β → R β₀) → R β
    rstep β IH ordβ β∈γ = go (ord-case β ordβ)
      where
      ihOrd : (β₀ : S) → ⟨ β₀ ∈ˢ β ⟩ → IsOrd β₀
      ihOrd β₀ h = mem-ord {A = β} ordβ β₀ h
      inγ : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ δ ∈ˢ γ ⟩
      inγ δ δ∈β = isLimit-ord γ limγ .fst {x = β} {y = δ} δ∈β β∈γ
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
              (IH δ δ∈β ordδ (inγ δ δ∈β) .snd) (slot∈L γ limγ)))
        where
        δ∈β : ⟨ δ ∈ˢ β ⟩
        δ∈β = subst (λ w → ⟨ δ ∈ˢ w ⟩) sδ≡β (self∈sucV δ)
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
            IH (sucV δ) sδ∈β (suc-ord (ihOrd δ δ∈β)) (inγ (sucV δ) sδ∈β) .fst v
              (subst (λ w → ⟨ v ∈ˢ w ⟩) (sym (Sset-suc δ)) hv)
            where
            sδ∈β : ⟨ sucV δ ∈ˢ β ⟩
            sδ∈β = limit-succ-mem β δ limβ δ∈β
        memFn : ⟨ Sset β ∈ˢ Lset γ ⟩
        memFn = below-lim γ limγ β ordβ limβ β∈γ

    rudBelow : (β : S) → IsOrd β → ⟨ β ∈ˢ γ ⟩ → RudBelow β γ
    rudBelow = ∈-induction rstep

  -- The surviving unconditional direction: a member of a rud level is a
  -- member of a constructible stage, read off the inclusion half of P(α) at
  -- the successor index the step decomposition supplies.
  bridge-isJ→isL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩
  bridge-isJ→isL x = PT.rec (snd (isL x)) go
    where
    go : Σ[ γ ∈ S ] (Σ[ lim ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ˢ Jset γ lim ⟩) → ⟨ isL x ⟩
    go (γ , lim , x∈J) = Lset→isL γ (isLimit-ord γ lim) x x∈L
      where
      x∈L : ⟨ x ∈ˢ Lset γ ⟩
      x∈L = PT.rec (snd (x ∈ˢ Lset γ)) atEnter (Sset-out γ x x∈J)
        where
        atEnter : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩)
                → ⟨ x ∈ˢ Lset γ ⟩
        atEnter (δ , δ∈γ , hx) =
          Below.rudBelow γ lim (sucV δ)
            (suc-ord (limit-mem-ord γ lim δ δ∈γ))
            (limit-succ-mem γ δ lim δ∈γ) .fst x
            (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) hx)
```
