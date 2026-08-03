# The rud step as a definable set

<!--en-->
Read against the constructible tower, one rud step over a set is a single
**definable subset** of a stage: the stage that already holds the set as a member
and every value the step adds. The defining formula is the disjunction of the two
floor clauses, "a member of the set" and "the set itself", with the sixteen
operation descriptions at **bound** argument variables, which is the one thing
the description chapter does not deliver, since there the arguments are
constants. The reading is taken in the inner world of the stage, where the
quantifiers range over the stage itself; nothing here has to be Δ₀, because the
definability operator accepts any formula at all, and the absoluteness machinery
never enters.

Beside that reading stands the mechanical half, which the bridge's reduction
consumes under its own name: every member of a one-step value lies **four**
stages above the stage that holds the arguments. Four is not a rounding: it is
exactly the price of the two tuple operations, whose values nest one Kuratowski
pair inside another, and each pair costs two stages.
<!--zh-->
对着可构造塔来读，一个集合之上的一步初步函数，是某个阶段的单个**可定义子集**：那个阶段已经把该集合作为成员收下，也收下该步所添的每个值。定义公式是两条地板子句 (「该集合的成员」与「该集合自身」) 与十六条运算描述的析取，而后者的实参取**受约束的变量**，这正是描述章未曾交付的一件事，因为那里的实参是常量。读法取在该阶段的内层世界里，量词遍历该阶段自身；此处无一需要 Δ₀，因为可定义性算子接纳任意公式，绝对性机制一步也不进场。

与这套读法并肩的是机械的一半，桥的归约以它自己的名字消费它：一步之值的每个成员都落在收下诸实参的阶段之上**四**个阶段处。四不是凑整：它恰是两个三元组运算的价钱，它们的值把一个 Kuratowski 对嵌进另一个之内，而每个对花费两个阶段。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.StepInL {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Rud.Ops {ℓ} using
  ( F0; F0-spec; F1-spec; F2-read; F2-write; F3-read; F3-write; F4-read
  ; F4-write; F5-spec; F6-read; F6-write; F7-read; F7-write )
open import L.Rud.Images {ℓ} using
  ( F8; F8-spec; F10; F10-spec; left; left-spec; right
  ; right-nonpair; ⋂; ⋂-member-in-all; left-⋂-collapse; left-⋂-empty
  ; module F15Of )
open import L.Rud.Describe {ℓ} using ( module F10Desc )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; Fof; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5
  ; Fof-f6; Fof-f7; Fof-f8; Fof-f9; Fof-f10; Fof-f11; Fof-f12; Fof-f13
  ; Fof-f14; Fof-f15; singl≡pair; isPair
  ; step; step-out; StepArm; arm-member; arm-self; arm-image
  ; step-in; step-in-self; step-in-img; u'; u'-in; u-self-in
  ; right-at-pair )
open import L.Rud.Bridge {ℓ} lem A using
  ( 𝒟ₒ⊆Lsuc; Ltr; Lpair; ValuesInU; suc⁴; empty-⊆; ext-⊆ )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; ⋃_; union-ax; module InfinitySet )
open import Cubical.Functions.Logic using ( ∃[]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Reading a pair inside a transitive set

The values of the sixteen operations are built from Kuratowski pairs, and every
argument of a rud step lies in a constructible stage. A transitive set that holds
a pair holds both of its components, two membership steps down through the
singleton and the unordered pair. The projections are total, so a set that is not
a pair still has a left and a right; the junk readings place both, and the empty
set is the only value that need not already be a member of the carrier.
<!--zh-->
## 在传递集内读一个对

十六个运算的值由 Kuratowski 对造出，而一步初步函数的每个实参都落在某个可构造阶段里。传递集若收下一个对，就收下它的两个分量：经单点集与无序对向下走两步隶属即可。投影是全函数，故非对之集仍有左右分量；垃圾读取把两者都安放好，而空集是唯一可能尚未属于载体的值。
<!--/-->

```agda
module Reads (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C)) where

  mem : (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
  mem x y y∈x x∈C = Ctr {x = x} {y = y} y∈x x∈C

  self∈singl : (p : S) → ⟨ p ∈ˢ ⁅ p ⁆s ⟩
  self∈singl p = subst (λ w → ⟨ p ∈ˢ w ⟩) (sym (singl≡pair p))
    (F0-spec p p p .snd ∣ inl refl ∣₁)

  prL∈ : (p q : S) → ⟨ pr p q ∈ˢ C ⟩ → ⟨ p ∈ˢ C ⟩
  prL∈ p q h = mem (⁅ p ⁆s) p (self∈singl p)
    (mem (pr p q) (⁅ p ⁆s) (F0-spec (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p ⁆s) .snd
      ∣ inl refl ∣₁) h)

  prR∈ : (p q : S) → ⟨ pr p q ∈ˢ C ⟩ → ⟨ q ∈ˢ C ⟩
  prR∈ p q h = mem (F0 p q) q (F0-spec p q q .snd ∣ inr refl ∣₁)
    (mem (pr p q) (F0 p q) (F0-spec (⁅ p ⁆s) (⁅ p , q ⁆) (⁅ p , q ⁆) .snd
      ∣ inr refl ∣₁) h)

  left-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
  left-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (left b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ left b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym left≡p)
        (prL∈ p q (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
        where
        left≡p : left b ≡ p
        left≡p = subst (λ w → left w ≡ p) (sym b≡) (left-spec p q)
    atPair (inr _) = atCap (lem (∃[ c ] (c ∈ₛ ⋂ b)))
      where
      atCap : ⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ ⊎ (⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ → Empty.⊥)
            → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
      atCap (inl e) = inl (PT.rec (snd (left b ∈ˢ C)) go e)
        where
        go : Σ[ c ∈ S ] ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ left b ∈ˢ C ⟩
        go (c , c∈⋂) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (left-⋂-collapse b c c∈⋂))
          (PT.rec (snd (c ∈ˢ C)) inC (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂))
          where
          inC : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ]
                      ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
                  (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
              → ⟨ c ∈ˢ C ⟩
          inC (p , _) = mem w c c∈w w∈C
            where
            w : S
            w = ⟪ b ⟫↪ (p .fst)
            w∈C : ⟨ w ∈ˢ C ⟩
            w∈C = mem b w (∈∈ₛ {a = w} {b = b} .snd (∈ₛ⟪ b ⟫↪ (p .fst))) b∈
            c∈w : ⟨ c ∈ˢ w ⟩
            c∈w = ∈∈ₛ {a = c} {b = w} .snd
              (⋂-member-in-all b c w c∈⋂ (∈ₛ⟪ b ⟫↪ (p .fst)))
      atCap (inr no) = inr (left-⋂-empty b (λ c h → no ∣ c , h ∣₁))

  right-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
  right-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (right b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ right b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (right-at-pair b p q b≡))
        (prR∈ p q (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
    atPair (inr nb) = inr (right-nonpair b (λ p q e → nb ∣ p , q , e ∣₁))
```

<!--en-->
## The sixteen values, over an abstract offset

The members of a one-step value are read operation by operation, and every read
lands in one of five shapes: a member of the carrier, an unordered pair of two
members, a Kuratowski pair, a Kuratowski pair nested once, and one image slice.
The offsets are therefore stated abstractly, as a telescope of closure facts over
three carriers, and instantiated once at the tower. Nothing in this module
mentions a stage, which is what keeps the sixteen goal types free of the
successor tower.
<!--zh-->
## 十六个值，在抽象偏移之上

单步值的诸成员逐运算读出，而每次读取都落进五种形状之一：载体的一个成员、两个成员的无序对、一个 Kuratowski 对、一次嵌套的 Kuratowski 对，以及一个像片。故偏移抽象地陈述，作为三个载体之上若干闭包事实的望远镜，只在塔处实例化一次。本模块不提及任何阶段，这正是让十六个目标类型不沾后继塔的办法。
<!--/-->

```agda
module Values (C P T : S)
  (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C))
  (sub : (x : S) → ⟨ x ∈ˢ C ⟩ → ⟨ x ∈ˢ P ⟩)
  (up : (x : S) → ⟨ x ∈ˢ P ⟩ → ⟨ x ∈ˢ T ⟩)
  (pairIn : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ F0 p q ∈ˢ T ⟩)
  (prIn : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ pr p q ∈ˢ T ⟩)
  (prIn₂ : (p q r : S) → ⟨ p ∈ˢ C ⟩ → ⟨ q ∈ˢ C ⟩ → ⟨ r ∈ˢ C ⟩
         → ⟨ pr p (pr q r) ∈ˢ T ⟩)
  (pairPrIn : (l p q : S) → ⟨ l ∈ˢ P ⟩ → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩
            → ⟨ F0 l (pr p q) ∈ˢ T ⟩)
  (sliceIn : (x y : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ F10 x y ∈ˢ T ⟩)
  (∅∈P : ⟨ ∅ ∈ˢ P ⟩)
  where

  open Reads C Ctr

  inP : (b : S) → (⟨ b ∈ˢ C ⟩ ⊎ (b ≡ ∅)) → ⟨ b ∈ˢ P ⟩
  inP b (inl h) = sub b h
  inP b (inr e) = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) ∅∈P

  module F15C = F15Of A

  valueMem : (i : Op16) (a b : S) → ⟨ a ∈ˢ C ⟩ → ⟨ b ∈ˢ C ⟩
           → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ T ⟩
  valueMem op0 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f0 a b) h))
    where
    go : (v ≡ a) ⊎ (v ≡ b) → ⟨ v ∈ˢ T ⟩
    go (inl e) = up v (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) (sub a a∈))
    go (inr e) = up v (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) (sub b b∈))
  valueMem op1 a b a∈ b∈ v h = up v (sub v
    (mem a v (F1-spec a b v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f1 a b) h) .fst) a∈))
  valueMem op2 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F2-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f2 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p q ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , p∈a , q∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn p q (sub p (mem a p p∈a a∈)) (sub q (mem b q q∈b b∈)))
  valueMem op3 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F3-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f3 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ z ∈ S ] Σ[ q ∈ S ]
           (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p (pr z q) ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , z , q , z∈a , pq∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn₂ p z q (prL∈ p q (mem b (pr p q) pq∈b b∈))
        (mem a z z∈a a∈) (prR∈ p q (mem b (pr p q) pq∈b b∈)))
  valueMem op4 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F4-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f4 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ z ∈ S ]
           (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p (pr q z) ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , z , z∈a , pq∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn₂ p q z (prL∈ p q (mem b (pr p q) pq∈b b∈))
        (prR∈ p q (mem b (pr p q) pq∈b b∈)) (mem a z z∈a a∈))
  valueMem op5 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F5-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f5 a b) h))
    where
    go : Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (v ∈ˢ w) ⟩ → ⟨ v ∈ˢ T ⟩
    go (w , w∈a , v∈w) = up v (sub v (mem w v v∈w (mem a w w∈a a∈)))
  valueMem op6 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F6-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f6 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ v ≡ₕ p ⟩) → ⟨ v ∈ˢ T ⟩
    go (p , q , pq∈a , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up p (sub p (prL∈ p q (mem a (pr p q) pq∈a a∈))))
  valueMem op7 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F7-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f7 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ]
           (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ v ≡ₕ pr p q ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , p∈a , q∈a , _ , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn p q (sub p (mem a p p∈a a∈)) (sub q (mem a q q∈a a∈)))
  valueMem op8 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (subst ⟨_⟩ (F8-spec a b v) (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f8 a b) h))
    where
    go : Σ[ m ∈ ⟪ b ⟫ ] (F10 a (⟪ b ⟫↪ m) ≡ v) → ⟨ v ∈ˢ T ⟩
    go (m , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) e
      (sliceIn a (⟪ b ⟫↪ m) a∈
        (mem b (⟪ b ⟫↪ m) (∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd (∈ₛ⟪ b ⟫↪ m)) b∈))
  valueMem op9 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f9 a b) h))
    where
    go : (v ≡ ⁅ a ⁆s) ⊎ (v ≡ ⁅ a , b ⁆) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair a))
      (pairIn a a (sub a a∈) (sub a a∈))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairIn a b (sub a a∈) (sub b b∈))
  valueMem op10 a b a∈ b∈ v h = up v (sub v
    (prR∈ b v (mem a (pr b v)
      (subst ⟨_⟩ (F10-spec a b v)
        (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f10 a b) h)) a∈)))
  valueMem op11 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f11 a b) h))
    where
    l∈ : ⟨ left b ∈ˢ P ⟩
    l∈ = inP (left b) (left-read b b∈)
    r∈ : ⟨ right b ∈ˢ P ⟩
    r∈ = inP (right b) (right-read b b∈)
    go : (v ≡ ⁅ left b ⁆s) ⊎ (v ≡ ⁅ left b , pr a (right b) ⁆) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair (left b)))
      (pairIn (left b) (left b) l∈ l∈)
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairPrIn (left b) a (right b) l∈ (sub a a∈) r∈)
  valueMem op12 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f12 a b) h))
    where
    l∈ : ⟨ left b ∈ˢ P ⟩
    l∈ = inP (left b) (left-read b b∈)
    r∈ : ⟨ right b ∈ˢ P ⟩
    r∈ = inP (right b) (right-read b b∈)
    go : (v ≡ ⁅ left b ⁆s) ⊎ (v ≡ ⁅ left b , pr (right b) a ⁆) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair (left b)))
      (pairIn (left b) (left b) l∈ l∈)
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairPrIn (left b) (right b) a l∈ r∈ (sub a a∈))
  valueMem op13 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (left b) (pr (right b) a) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f13 a b) h))
    where
    go : (v ≡ left b) ⊎ (v ≡ pr (right b) a) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up (left b) (inP (left b) (left-read b b∈)))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn (right b) a (inP (right b) (right-read b b∈)) (sub a a∈))
  valueMem op14 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (left b) (pr a (right b)) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f14 a b) h))
    where
    go : (v ≡ left b) ⊎ (v ≡ pr a (right b)) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up (left b) (inP (left b) (left-read b b∈)))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn a (right b) (sub a a∈) (inP (right b) (right-read b b∈)))
  valueMem op15 a b a∈ b∈ v h = up v (sub v (mem a v
    (subst ⟨_⟩ (F15C.F15-spec a v)
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f15 a b) h) .fst) a∈))
```

<!--en-->
## The offsets at the tower

Four stages above the stage that holds the argument, and no more. The count is
forced by the nested pair of the two tuple operations: a Kuratowski pair of two
members of a stage costs two stages, and the middle insertion pairs twice. The
closure facts are discharged here by pairing alone, plus one image slice, which
is a definable subset of the stage its two arguments live in, and the empty set,
which is the definable subset carved by the false formula.
<!--zh-->
## 塔处的偏移

在收下实参的阶段之上四个阶段，不多不少。这个计数由两个三元组运算的嵌套对逼出：一个阶段的两个成员之 Kuratowski 对花费两个阶段，而中间插入配对两次。诸闭包事实在此仅由配对兑现，外加一个像片 (它是其两个实参所在阶段的一个可定义子集) 与空集 (它是假公式刻出的可定义子集)。
<!--/-->

```agda
defSet⊥≡∅ : (D : S) → DefOf.defSet D ⊥̇ ≡ ∅
defSet⊥≡∅ D = empty-⊆ (DefOf.defSet D ⊥̇) no
  where
  no : (x : S) → ⟨ x ∈ˢ DefOf.defSet D ⊥̇ ⟩ → Empty.⊥
  no x h = Empty.rec* (subst ⟨_⟩ (DefOf.defSet-mem D ⊥̇ (fib .fst))
    (subst (λ w → ⟨ w ∈ˢ DefOf.defSet D ⊥̇ ⟩) (sym (fib .snd)) h))
    where
    fib : Σ[ m ∈ ⟪ D ⟫ ] (⟪ D ⟫↪ m ≡ x)
    fib = ∈-asFiber {a = x} {b = D} (DefOf.defSet⊆A D ⊥̇ x h)

∅∈Lsuc : (ξ : S) → ⟨ ∅ ∈ˢ Lset (sucV ξ) ⟩
∅∈Lsuc ξ = subst (λ w → ⟨ w ∈ˢ Lset (sucV ξ) ⟩) (defSet⊥≡∅ (Lset ξ))
  (𝒟ₒ⊆Lsuc ξ (DefOf.defSet (Lset ξ) ⊥̇)
    (𝒟ₒ-intro (Lset ξ) (DefOf.defSet (Lset ξ) ⊥̇) ∣ ⊥̇ , refl ∣₁))

sliceInLsuc : (ξ x y : S) → ⟨ x ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset ξ ⟩
            → ⟨ F10 x y ∈ˢ Lset (sucV ξ) ⟩
sliceInLsuc ξ x y x∈ y∈ = 𝒟ₒ⊆Lsuc ξ (F10 x y)
  (𝒟ₒ-intro (Lset ξ) (F10 x y) ∣ D.Φ₁₀ , D.F10-defSet≡ ∣₁)
  where
  module D = F10Desc (Lset ξ) x y x∈ y∈ (Ltr ξ)

opaque
  unfolding suc⁴
  -- perf: P-i layer cap; the four exposed successor layers stay in this block
  values∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ValuesInU u (suc⁴ ζ)
  values∈L u ζ u∈ i a b sa sb v h =
    Val.valueMem i a b (split a sa) (split b sb) v h
    where
    ζ₁ ζ₂ ζ₃ ζ₄ : S
    ζ₁ = sucV ζ
    ζ₂ = sucV ζ₁
    ζ₃ = sucV ζ₂
    ζ₄ = sucV ζ₃
    up₁ : (ξ y : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
    up₁ ξ y k = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) k
    subFn : (x : S) → ⟨ x ∈ˢ Lset ζ ⟩ → ⟨ x ∈ˢ Lset ζ₁ ⟩
    subFn = up₁ ζ
    upFn : (x : S) → ⟨ x ∈ˢ Lset ζ₁ ⟩ → ⟨ x ∈ˢ Lset ζ₄ ⟩
    upFn x k = up₁ ζ₃ x (up₁ ζ₂ x (up₁ ζ₁ x k))
    pairFn : (p q : S) → ⟨ p ∈ˢ Lset ζ₁ ⟩ → ⟨ q ∈ˢ Lset ζ₁ ⟩
           → ⟨ F0 p q ∈ˢ Lset ζ₄ ⟩
    pairFn p q p∈ q∈ = up₁ ζ₃ (F0 p q) (up₁ ζ₂ (F0 p q) (Lpair ζ₁ p q p∈ q∈))
    prFn : (p q : S) → ⟨ p ∈ˢ Lset ζ₁ ⟩ → ⟨ q ∈ˢ Lset ζ₁ ⟩
         → ⟨ pr p q ∈ˢ Lset ζ₄ ⟩
    prFn p q p∈ q∈ = up₁ ζ₃ (pr p q)
      (Lpair ζ₂ (⁅ p ⁆s) (⁅ p , q ⁆) sgl∈ pair∈)
      where
      sgl∈ : ⟨ ⁅ p ⁆s ∈ˢ Lset ζ₂ ⟩
      sgl∈ = subst (λ w → ⟨ w ∈ˢ Lset ζ₂ ⟩) (sym (singl≡pair p))
        (Lpair ζ₁ p p p∈ p∈)
      pair∈ : ⟨ ⁅ p , q ⁆ ∈ˢ Lset ζ₂ ⟩
      pair∈ = Lpair ζ₁ p q p∈ q∈
    prFn₂ : (p q r : S) → ⟨ p ∈ˢ Lset ζ ⟩ → ⟨ q ∈ˢ Lset ζ ⟩ → ⟨ r ∈ˢ Lset ζ ⟩
          → ⟨ pr p (pr q r) ∈ˢ Lset ζ₄ ⟩
    prFn₂ p q r p∈ q∈ r∈ = Lpair ζ₃ (⁅ p ⁆s) (⁅ p , pr q r ⁆) sgl∈ pair∈
      where
      inner : ⟨ pr q r ∈ˢ Lset ζ₂ ⟩
      inner = Lpair ζ₁ (⁅ q ⁆s) (⁅ q , r ⁆)
        (subst (λ w → ⟨ w ∈ˢ Lset ζ₁ ⟩) (sym (singl≡pair q))
          (Lpair ζ q q q∈ q∈))
        (Lpair ζ q r q∈ r∈)
      p∈₂ : ⟨ p ∈ˢ Lset ζ₂ ⟩
      p∈₂ = up₁ ζ₁ p (up₁ ζ p p∈)
      sgl∈ : ⟨ ⁅ p ⁆s ∈ˢ Lset ζ₃ ⟩
      sgl∈ = subst (λ w → ⟨ w ∈ˢ Lset ζ₃ ⟩) (sym (singl≡pair p))
        (Lpair ζ₂ p p p∈₂ p∈₂)
      pair∈ : ⟨ ⁅ p , pr q r ⁆ ∈ˢ Lset ζ₃ ⟩
      pair∈ = Lpair ζ₂ p (pr q r) p∈₂ inner
    pairPrFn : (l p q : S) → ⟨ l ∈ˢ Lset ζ₁ ⟩ → ⟨ p ∈ˢ Lset ζ₁ ⟩
             → ⟨ q ∈ˢ Lset ζ₁ ⟩ → ⟨ F0 l (pr p q) ∈ˢ Lset ζ₄ ⟩
    pairPrFn l p q l∈ p∈ q∈ =
      Lpair ζ₃ l (pr p q) (up₁ ζ₂ l (up₁ ζ₁ l l∈)) inner
      where
      inner : ⟨ pr p q ∈ˢ Lset ζ₃ ⟩
      inner = Lpair ζ₂ (⁅ p ⁆s) (⁅ p , q ⁆)
        (subst (λ w → ⟨ w ∈ˢ Lset ζ₂ ⟩) (sym (singl≡pair p))
          (Lpair ζ₁ p p p∈ p∈))
        (Lpair ζ₁ p q p∈ q∈)
    sliceFn : (x y : S) → ⟨ x ∈ˢ Lset ζ ⟩ → ⟨ y ∈ˢ Lset ζ ⟩
            → ⟨ F10 x y ∈ˢ Lset ζ₄ ⟩
    sliceFn x y x∈ y∈ = upFn (F10 x y) (sliceInLsuc ζ x y x∈ y∈)
    module Val = Values (Lset ζ) (Lset ζ₁) (Lset ζ₄) (Ltr ζ) subFn upFn
                 pairFn prFn prFn₂ pairPrFn sliceFn (∅∈Lsuc ζ)
    split : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ Lset ζ ⟩
    split c (inl c∈u) = Ltr ζ {x = u} {y = c} c∈u u∈
    split c (inr c≡u) = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym c≡u) u∈
```

<!--en-->
## The inner world, read directly

A definable subset of a stage is carved by a formula whose quantifiers range over
the stage itself, and that is the only reading used from here on. Nothing below
is Δ₀: the operator takes any formula at all, so the descriptions may quantify
without a bound, and the absoluteness machinery never enters. What the reading
needs is one frame, "this formula carves exactly this set", stated with the
environment spelled out and the membership certificate carried beside the
element.
<!--zh-->
## 直接读内层世界

一个阶段的可定义子集由一条公式刻出，其量词遍历该阶段自身，而自此以下只用这一种读法。以下没有任何 Δ₀ 的要求：算子接纳任意公式，故诸描述可以无界量化，绝对性机制一步也不进场。这套读法所需的只有一个框架，即「此公式恰好刻出此集」，其中环境逐项写明，隶属证书与元素并肩携带。
<!--/-->

```agda
private
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero
  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc f0
  f2 : {n : ℕ} → Fin (suc (suc (suc n)))
  f2 = suc f1
  f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  f3 = suc f2
  f4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
  f4 = suc f3
  f5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
  f5 = suc f4
  f6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  f6 = suc f5

module Desc (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C)) where

  open Reads C Ctr

  module DefC = DefOf C

  pt : (x : S) → ⟨ x ∈ˢ C ⟩ → DefC.SM
  pt x h = x , h

  envι : (m : ⟪ C ⟫) (x : S) (x∈ : ⟨ x ∈ˢ C ⟩) → ⟪ C ⟫↪ m ≡ x
       → DefC.ι m ≡ pt x x∈
  envι m x x∈ q = Σ≡Prop (λ w → snd (w ∈ˢ C)) q

  described : (Φ : Formula ⟪ C ⟫ 1) (W : S)
            → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
               → ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ Φ ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ Φ ⟩
               → ⟨ v ∈ˢ W ⟩)
            → DefC.defSet Φ ≡ W
  described Φ W wsub din dout = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ DefC.defSet Φ ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = dout x x∈ sat
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = DefC.defSet⊆A Φ x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
      sat : ⟨ (pt x x∈ ∷ []) DefC.⊨ᵐ Φ ⟩
      sat = subst (λ e → ⟨ (e ∷ []) DefC.⊨ᵐ Φ ⟩) (envι (fib .fst) x x∈ (fib .snd))
        (subst ⟨_⟩ (DefC.defSet-mem Φ (fib .fst))
          (subst (λ w → ⟨ w ∈ˢ DefC.defSet Φ ⟩) (sym (fib .snd)) h))
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ DefC.defSet Φ ⟩
    sup x h = subst (λ w → ⟨ w ∈ˢ DefC.defSet Φ ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (DefC.defSet-mem Φ (fib .fst)))
        (subst (λ e → ⟨ (e ∷ []) DefC.⊨ᵐ Φ ⟩)
          (sym (envι (fib .fst) x x∈ (fib .snd))) (din x x∈ h)))
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = wsub x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
```

<!--en-->
## Singletons, unordered pairs, and the ordered pair

Three descriptions, each read at variables rather than at constants, because the
arguments of the operations will be bound by quantifiers. The singleton and the
unordered pair are characterized by membership plus a closure clause, and the
ordered pair by the two members of its Kuratowski form. Every quantifier here is
bounded by a variable whose value is a member of the carrier, so the relativized
reading is faithful: the members of a member are members.
<!--zh-->
## 单点集、无序对与有序对

三条描述，都读在变量而非常量上，因为诸运算的实参将被量词约束。单点集与无序对由隶属加一条闭合子句刻画，有序对则由其 Kuratowski 形式的两个成员刻画。此处每个量词都以取值为载体成员的变量为界，故相对化读法忠实：成员之成员仍是成员。
<!--/-->

```agda
  singl-eq : (x p : S) → ⟨ x ∈ˢ ⁅ p ⁆s ⟩ → x ≡ p
  singl-eq x p h = PT.rec (setIsSet x p) (Sum.rec (λ e → e) (λ e → e))
    (F0-spec p p x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) (singl≡pair p) h))

  sglChar : (w p : S) → ⟨ p ∈ˢ w ⟩ → ((z : S) → ⟨ z ∈ˢ w ⟩ → z ≡ p)
          → w ≡ ⁅ p ⁆s
  sglChar w p p∈ all = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ w ⟩ → ⟨ x ∈ˢ ⁅ p ⁆s ⟩
    sub x h = subst (λ t → ⟨ t ∈ˢ ⁅ p ⁆s ⟩) (sym (all x h)) (self∈singl p)
    sup : (x : S) → ⟨ x ∈ˢ ⁅ p ⁆s ⟩ → ⟨ x ∈ˢ w ⟩
    sup x h = subst (λ t → ⟨ t ∈ˢ w ⟩) (sym (singl-eq x p h)) p∈

  pairChar : (w p q : S) → ⟨ p ∈ˢ w ⟩ → ⟨ q ∈ˢ w ⟩
           → ((z : S) → ⟨ z ∈ˢ w ⟩ → ∥ (z ≡ p) ⊎ (z ≡ q) ∥₁)
           → w ≡ ⁅ p , q ⁆
  pairChar w p q p∈ q∈ all = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ w ⟩ → ⟨ x ∈ˢ ⁅ p , q ⁆ ⟩
    sub x h = PT.rec (snd (x ∈ˢ ⁅ p , q ⁆)) go (all x h)
      where
      go : (x ≡ p) ⊎ (x ≡ q) → ⟨ x ∈ˢ ⁅ p , q ⁆ ⟩
      go (inl e) = F0-spec p q x .snd ∣ inl e ∣₁
      go (inr e) = F0-spec p q x .snd ∣ inr e ∣₁
    sup : (x : S) → ⟨ x ∈ˢ ⁅ p , q ⁆ ⟩ → ⟨ x ∈ˢ w ⟩
    sup x h = PT.rec (snd (x ∈ˢ w)) go (F0-spec p q x .fst h)
      where
      go : (x ≡ p) ⊎ (x ≡ q) → ⟨ x ∈ˢ w ⟩
      go (inl e) = subst (λ t → ⟨ t ∈ˢ w ⟩) (sym e) p∈
      go (inr e) = subst (λ t → ⟨ t ∈ˢ w ⟩) (sym e) q∈

  sglAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  sglAt k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var f0 ≐ var (suc i)))

  pairAt : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ C ⟫ n
  pairAt k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
             ∧̇ (∀̇∈ (var k) ((var f0 ≐ var (suc i)) ∨̇ (var f0 ≐ var (suc j)))))

  prAt : {n : ℕ} → Fin n → Fin n → Fin n → Formula ⟪ C ⟫ n
  prAt q u v = (∃̇∈ (var q) (sglAt f0 (suc u)))
            ∧̇ ((∃̇∈ (var q) (pairAt f0 (suc u) (suc v)))
            ∧̇ (∀̇∈ (var q) (sglAt f0 (suc u) ∨̇ pairAt f0 (suc u) (suc v))))

  entry∈ : {n : ℕ} (k : Fin n) (δ : Vec DefC.SM n) (z : S)
         → ⟨ z ∈ˢ fst (lookup k δ) ⟩ → ⟨ z ∈ˢ C ⟩
  entry∈ k δ z h = mem (fst (lookup k δ)) z h (snd (lookup k δ))

  sglAt-out : {n : ℕ} (k i : Fin n) (δ : Vec DefC.SM n)
            → ⟨ δ DefC.⊨ᵐ sglAt k i ⟩
            → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) ⁆s
  sglAt-out k i δ (h₁ , h₂) =
    sglChar (fst (lookup k δ)) (fst (lookup i δ)) h₁ all
    where
    all : (z : S) → ⟨ z ∈ˢ fst (lookup k δ) ⟩ → z ≡ fst (lookup i δ)
    all z z∈ = h₂ (pt z (entry∈ k δ z z∈)) z∈

  sglAt-in : {n : ℕ} (k i : Fin n) (δ : Vec DefC.SM n)
           → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) ⁆s
           → ⟨ δ DefC.⊨ᵐ sglAt k i ⟩
  sglAt-in k i δ e = (self∈ , all)
    where
    self∈ : ⟨ fst (lookup i δ) ∈ˢ fst (lookup k δ) ⟩
    self∈ = subst (λ w → ⟨ fst (lookup i δ) ∈ˢ w ⟩) (sym e)
      (self∈singl (fst (lookup i δ)))
    all : (xm : DefC.SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
        → fst xm ≡ fst (lookup i δ)
    all xm h = singl-eq (fst xm) (fst (lookup i δ))
      (subst (λ w → ⟨ fst xm ∈ˢ w ⟩) e h)

  pairAt-out : {n : ℕ} (k i j : Fin n) (δ : Vec DefC.SM n)
             → ⟨ δ DefC.⊨ᵐ pairAt k i j ⟩
             → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) , fst (lookup j δ) ⁆
  pairAt-out k i j δ (h₁ , (h₂ , h₃)) =
    pairChar (fst (lookup k δ)) (fst (lookup i δ)) (fst (lookup j δ)) h₁ h₂ all
    where
    all : (z : S) → ⟨ z ∈ˢ fst (lookup k δ) ⟩
        → ∥ (z ≡ fst (lookup i δ)) ⊎ (z ≡ fst (lookup j δ)) ∥₁
    all z z∈ = h₃ (pt z (entry∈ k δ z z∈)) z∈

  pairAt-in : {n : ℕ} (k i j : Fin n) (δ : Vec DefC.SM n)
            → fst (lookup k δ) ≡ ⁅ fst (lookup i δ) , fst (lookup j δ) ⁆
            → ⟨ δ DefC.⊨ᵐ pairAt k i j ⟩
  pairAt-in k i j δ e = (i∈ , (j∈ , all))
    where
    i∈ : ⟨ fst (lookup i δ) ∈ˢ fst (lookup k δ) ⟩
    i∈ = subst (λ w → ⟨ fst (lookup i δ) ∈ˢ w ⟩) (sym e)
      (F0-spec (fst (lookup i δ)) (fst (lookup j δ)) (fst (lookup i δ)) .snd
        ∣ inl refl ∣₁)
    j∈ : ⟨ fst (lookup j δ) ∈ˢ fst (lookup k δ) ⟩
    j∈ = subst (λ w → ⟨ fst (lookup j δ) ∈ˢ w ⟩) (sym e)
      (F0-spec (fst (lookup i δ)) (fst (lookup j δ)) (fst (lookup j δ)) .snd
        ∣ inr refl ∣₁)
    all : (xm : DefC.SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
        → ∥ (fst xm ≡ fst (lookup i δ)) ⊎ (fst xm ≡ fst (lookup j δ)) ∥₁
    all xm h = F0-spec (fst (lookup i δ)) (fst (lookup j δ)) (fst xm) .fst
      (subst (λ w → ⟨ fst xm ∈ˢ w ⟩) e h)

  prAt-out : {n : ℕ} (q u v : Fin n) (δ : Vec DefC.SM n)
           → ⟨ δ DefC.⊨ᵐ prAt q u v ⟩
           → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
  prAt-out q u v δ (h₁ , (h₂ , h₃)) =
    PT.rec (setIsSet (fst (lookup q δ)) (pr (fst (lookup u δ)) (fst (lookup v δ))))
      (λ w₁ → PT.rec (setIsSet (fst (lookup q δ))
                       (pr (fst (lookup u δ)) (fst (lookup v δ))))
        (go w₁) h₂) h₁
    where
    Q U W : S
    Q = fst (lookup q δ)
    U = fst (lookup u δ)
    W = fst (lookup v δ)
    all : (z : S) → ⟨ z ∈ˢ Q ⟩ → ∥ (z ≡ ⁅ U ⁆s) ⊎ (z ≡ ⁅ U , W ⁆) ∥₁
    all z z∈ = PT.map pick (h₃ (pt z (entry∈ q δ z z∈)) z∈)
      where
      pick : ⟨ (pt z (entry∈ q δ z z∈) ∷ δ) DefC.⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (pt z (entry∈ q δ z z∈) ∷ δ) DefC.⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
           → (z ≡ ⁅ U ⁆s) ⊎ (z ≡ ⁅ U , W ⁆)
      pick (inl s) = inl (sglAt-out f0 (suc u) (pt z (entry∈ q δ z z∈) ∷ δ) s)
      pick (inr s) =
        inr (pairAt-out f0 (suc u) (suc v) (pt z (entry∈ q δ z z∈) ∷ δ) s)
    go : Σ[ xm ∈ DefC.SM ] ⟨ (fst xm ∈ˢ Q)
           ⊓ ((xm ∷ δ) DefC.⊨ᵐ sglAt f0 (suc u)) ⟩
       → Σ[ ym ∈ DefC.SM ] ⟨ (fst ym ∈ˢ Q)
           ⊓ ((ym ∷ δ) DefC.⊨ᵐ pairAt f0 (suc u) (suc v)) ⟩
       → Q ≡ pr U W
    go (xm , (x∈Q , sx)) (ym , (y∈Q , sy)) = pairChar Q (⁅ U ⁆s) (⁅ U , W ⁆)
      (subst (λ t → ⟨ t ∈ˢ Q ⟩) (sglAt-out f0 (suc u) (xm ∷ δ) sx) x∈Q)
      (subst (λ t → ⟨ t ∈ˢ Q ⟩) (pairAt-out f0 (suc u) (suc v) (ym ∷ δ) sy) y∈Q)
      all

  prAt-in : {n : ℕ} (q u v : Fin n) (δ : Vec DefC.SM n)
          → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
          → ⟨ δ DefC.⊨ᵐ prAt q u v ⟩
  prAt-in q u v δ e = (part₁ , (part₂ , part₃))
    where
    Q U W : S
    Q = fst (lookup q δ)
    U = fst (lookup u δ)
    W = fst (lookup v δ)
    sgl∈Q : ⟨ ⁅ U ⁆s ∈ˢ Q ⟩
    sgl∈Q = subst (λ t → ⟨ ⁅ U ⁆s ∈ˢ t ⟩) (sym e)
      (F0-spec (⁅ U ⁆s) (⁅ U , W ⁆) (⁅ U ⁆s) .snd ∣ inl refl ∣₁)
    pair∈Q : ⟨ ⁅ U , W ⁆ ∈ˢ Q ⟩
    pair∈Q = subst (λ t → ⟨ ⁅ U , W ⁆ ∈ˢ t ⟩) (sym e)
      (F0-spec (⁅ U ⁆s) (⁅ U , W ⁆) (⁅ U , W ⁆) .snd ∣ inr refl ∣₁)
    part₁ : ⟨ δ DefC.⊨ᵐ (∃̇∈ (var q) (sglAt f0 (suc u))) ⟩
    part₁ = ∣ pt (⁅ U ⁆s) (entry∈ q δ (⁅ U ⁆s) sgl∈Q)
            , (sgl∈Q
              , sglAt-in f0 (suc u)
                  (pt (⁅ U ⁆s) (entry∈ q δ (⁅ U ⁆s) sgl∈Q) ∷ δ) refl) ∣₁
    part₂ : ⟨ δ DefC.⊨ᵐ (∃̇∈ (var q) (pairAt f0 (suc u) (suc v))) ⟩
    part₂ = ∣ pt (⁅ U , W ⁆) (entry∈ q δ (⁅ U , W ⁆) pair∈Q)
            , (pair∈Q
              , pairAt-in f0 (suc u) (suc v)
                  (pt (⁅ U , W ⁆) (entry∈ q δ (⁅ U , W ⁆) pair∈Q) ∷ δ) refl) ∣₁
    part₃ : ⟨ δ DefC.⊨ᵐ (∀̇∈ (var q)
              (sglAt f0 (suc u) ∨̇ pairAt f0 (suc u) (suc v))) ⟩
    part₃ xm h = PT.map pick
      (F0-spec (⁅ U ⁆s) (⁅ U , W ⁆) (fst xm) .fst
        (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h))
      where
      pick : (fst xm ≡ ⁅ U ⁆s) ⊎ (fst xm ≡ ⁅ U , W ⁆)
           → ⟨ (xm ∷ δ) DefC.⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (xm ∷ δ) DefC.⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
      pick (inl s) = inl (sglAt-in f0 (suc u) (xm ∷ δ) s)
      pick (inr s) = inr (pairAt-in f0 (suc u) (suc v) (xm ∷ δ) s)
```

<!--en-->
## The equality frame

One frame carries every "this variable is that set" clause below: read the
members of the variable through a body formula, and read the body back into the
variable. Given that the body describes a set whose members are all in the
carrier, the two halves are extensionality, and the frame is the only place where
that argument is made.
<!--zh-->
## 等词框架

以下每一条「此变量即彼集」的子句都由一个框架承载：把该变量的成员经一条公式体读出，再把公式体读回该变量。只要公式体所描述之集的成员全在载体内，两半合起来就是外延性，而该论证只在此框架处做一次。
<!--/-->

```agda
  eqFrame : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n) → Formula ⟪ C ⟫ n
  eqFrame k M = (∀̇∈ (var k) M) ∧̇ (∀̇ (M ⇒̇ (var f0 ∈̇ var (suc k))))

  eqFrame-out : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                (δ : Vec DefC.SM n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ M ⟩
                 → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                 → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ M ⟩)
              → ⟨ δ DefC.⊨ᵐ eqFrame k M ⟩ → fst (lookup k δ) ≡ W
  eqFrame-out k M δ W wsub mout min (h₁ , h₂) = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ fst (lookup k δ) ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = mout x (entry∈ k δ x h) (h₁ (pt x (entry∈ k δ x h)) h)
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ fst (lookup k δ) ⟩
    sup x h = h₂ (pt x (wsub x h)) (min x (wsub x h) h)

  eqFrame-in : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
               (δ : Vec DefC.SM n) (W : S)
             → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ M ⟩
                → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ M ⟩)
             → fst (lookup k δ) ≡ W → ⟨ δ DefC.⊨ᵐ eqFrame k M ⟩
  eqFrame-in k M δ W wsub mout min e = (part₁ , part₂)
    where
    part₁ : (xm : DefC.SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
          → ⟨ (xm ∷ δ) DefC.⊨ᵐ M ⟩
    part₁ xm h = min (fst xm) (snd xm)
      (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h)
    part₂ : (xm : DefC.SM) → ⟨ (xm ∷ δ) DefC.⊨ᵐ M ⟩
          → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
    part₂ xm h = subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (sym e)
      (mout (fst xm) (snd xm) h)
```

<!--en-->
## The sixteen memberships, at bound arguments

Here is the difference between this chapter and the description chapter: there
the two arguments of an operation were constants, one formula per pair of
arguments; here they are **variables**, because the step quantifies over them.
Each formula below says "the first variable is a member of the value of this
operation at the third and second variables", with the fourth variable reserved
for the value itself. The readings of the operations chapter are consumed
directly, one per clause.
<!--zh-->
## 十六条隶属，在受约束的实参上

本章与描述章的分别在此：那里一个运算的两个实参是常量，一对实参一条公式；此处它们是**变量**，因为 step 对它们量化。以下每条公式都说「第一个变量属于本运算在第三、第二个变量处的值」，第四个变量留给该值自身。运算章的诸读引理逐子句直接消费。
<!--/-->

```agda
  isPairF : {n : ℕ} → Fin n → Formula ⟪ C ⟫ n
  isPairF bk = ∃̇ (∃̇ (prAt (suc (suc bk)) f1 f0))

  unionMem : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  unionMem wk = ∃̇∈ (var (suc wk)) (var f1 ∈̇ var f0)

  unionEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  unionEq ck wk = eqFrame ck (unionMem wk)

  capF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  capF bk ck = (∃̇∈ (var bk) (unionEq (suc ck) f0))
             ∧̇ (∀̇∈ (var bk) (var (suc ck) ∈̇ var f0))

  leftMem : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  leftMem bk = ∃̇ (capF (suc (suc bk)) f0 ∧̇ (var f1 ∈̇ var f0))

  leftEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  leftEqF lk bk = eqFrame lk (leftMem bk)

  rightEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  rightEqF rk bk =
    (∃̇ (∃̇ (prAt (suc (suc bk)) f1 f0 ∧̇ (var (suc (suc rk)) ≐ var f0))))
    ∨̇ ((¬̇ isPairF bk) ∧̇ (∀̇∈ (var rk) ⊥̇))

```

<!--en-->
## The intersection, the union, and the two projections

The four tuple operations reach their arguments through the projections, which
are total: on a pair they are the two components, and off a pair they are junk.
The junk has to be described as exactly as the rest, and the left projection is
where the description is prettiest: `left b` is the union of the intersection of
`b` at **every** `b`, so one equality frame describes it with no case analysis
and no classical step. The intersection's own membership unfolds to two clauses,
"the candidate is the union of some member" and "the candidate lies in every
member", which is what the frame's body says. The right projection keeps a case
split, because off a pair it is the empty set by a separate reading.
<!--zh-->
## 交、并，与两个投影

四个三元组运算经投影够到实参，而投影是全函数：在对上它们是两个分量，不在对上则是垃圾。垃圾必须描述得与其余部分一样精确，而左投影正是描述最漂亮之处：`left b` 在**每个** `b` 处都是 `b` 之交的并，故一个等词框架即可描述它，无须情形分析，也无须经典一步。交自身的隶属展开为两条子句，「候选者是某个成员之并」与「候选者落在每个成员之中」，这正是框架体所说的。右投影保留情形分裂，因为不在对上时它由另一条读引理给出空集。
<!--/-->

```agda
cap-out : (b c : S) → ⟨ c ∈ˢ ⋂ b ⟩
        → ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w)) ∥₁
cap-out b c h = PT.map go h
  where
  go : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
         (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
     → Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w))
  go (p , q) = ⟪ b ⟫↪ (p .fst)
    , (∈∈ₛ {a = ⟪ b ⟫↪ (p .fst)} {b = b} .snd (∈ₛ⟪ b ⟫↪ (p .fst)) , sym q)

cap-all : (b c : S) → ⟨ c ∈ˢ ⋂ b ⟩ → (w : S) → ⟨ w ∈ˢ b ⟩ → ⟨ c ∈ˢ w ⟩
cap-all b c h w w∈b = ∈∈ₛ {a = c} {b = w} .snd
  (⋂-member-in-all b c w (∈∈ₛ {a = c} {b = ⋂ b} .fst h)
    (∈∈ₛ {a = w} {b = b} .fst w∈b))

cap-in : (b c w : S) → ⟨ w ∈ˢ b ⟩ → (c ≡ ⋃ w)
       → ((v : S) → ⟨ v ∈ˢ b ⟩ → ⟨ c ∈ˢ v ⟩) → ⟨ c ∈ˢ ⋂ b ⟩
cap-in b c w w∈b e all = ∣ (fib .fst , cond) , path ∣₁
  where
  fib : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ w)
  fib = ∈-asFiber {a = w} {b = b} w∈b
  path : ⋃ (⟪ b ⟫↪ (fib .fst)) ≡ c
  path = cong ⋃_ (fib .snd) ∙ sym e
  cond : (k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ (fib .fst)) ∈ₛ ⟪ b ⟫↪ k ⟩
  cond k = ∈∈ₛ {a = ⋃ (⟪ b ⟫↪ (fib .fst))} {b = ⟪ b ⟫↪ k} .fst
    (subst (λ t → ⟨ t ∈ˢ ⟪ b ⟫↪ k ⟩) (sym path)
      (all (⟪ b ⟫↪ k) (∈∈ₛ {a = ⟪ b ⟫↪ k} {b = b} .snd (∈ₛ⟪ b ⟫↪ k))))
```

```agda
module Frames (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C)) where

  open Reads C Ctr
  open Desc C Ctr

  cap∈ : (b c : S) → ⟨ b ∈ˢ C ⟩ → ⟨ c ∈ˢ ⋂ b ⟩ → ⟨ c ∈ˢ C ⟩
  cap∈ b c b∈ h = PT.rec (snd (c ∈ˢ C)) go (cap-out b c h)
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w)) → ⟨ c ∈ˢ C ⟩
    go (w , (w∈b , _)) = mem w c (cap-all b c h w w∈b) (mem b w w∈b b∈)

  unionSub : (w v : S) → ⟨ w ∈ˢ C ⟩ → ⟨ v ∈ˢ (⋃ w) ⟩ → ⟨ v ∈ˢ C ⟩
  unionSub w v w∈ h = PT.rec (snd (v ∈ˢ C)) go
    (union-ax w v .fst (∈∈ₛ {a = v} {b = ⋃ w} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ w ⟩ × ⟨ v ∈ₛ t ⟩) → ⟨ v ∈ˢ C ⟩
    go (t , (t∈w , v∈t)) = mem t v (∈∈ₛ {a = v} {b = t} .snd v∈t)
      (mem w t (∈∈ₛ {a = t} {b = w} .snd t∈w) w∈)

  unionMem-out : {n : ℕ} (wk : Fin n) (δ : Vec DefC.SM n) (v : S)
                 (v∈ : ⟨ v ∈ˢ C ⟩)
               → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ unionMem wk ⟩
               → ⟨ v ∈ˢ (⋃ (fst (lookup wk δ))) ⟩
  unionMem-out wk δ v v∈ h = ∈∈ₛ {a = v} {b = ⋃ (fst (lookup wk δ))} .snd
    (union-ax (fst (lookup wk δ)) v .snd (PT.map go h))
    where
    go : Σ[ tm ∈ DefC.SM ] ⟨ (fst tm ∈ˢ fst (lookup wk δ)) ⊓ (v ∈ˢ fst tm) ⟩
       → Σ[ t ∈ S ] (⟨ t ∈ₛ fst (lookup wk δ) ⟩ × ⟨ v ∈ₛ t ⟩)
    go (tm , (t∈w , v∈t)) = fst tm
      , (∈∈ₛ {a = fst tm} {b = fst (lookup wk δ)} .fst t∈w
        , ∈∈ₛ {a = v} {b = fst tm} .fst v∈t)

  unionMem-in : {n : ℕ} (wk : Fin n) (δ : Vec DefC.SM n) (v : S)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ v ∈ˢ (⋃ (fst (lookup wk δ))) ⟩
              → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ unionMem wk ⟩
  unionMem-in wk δ v v∈ h = PT.map go
    (union-ax (fst (lookup wk δ)) v .fst
      (∈∈ₛ {a = v} {b = ⋃ (fst (lookup wk δ))} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ fst (lookup wk δ) ⟩ × ⟨ v ∈ₛ t ⟩)
       → Σ[ tm ∈ DefC.SM ] ⟨ (fst tm ∈ˢ fst (lookup wk δ)) ⊓ (v ∈ˢ fst tm) ⟩
    go (t , (t∈w , v∈t)) = pt t (mem (fst (lookup wk δ)) t
        (∈∈ₛ {a = t} {b = fst (lookup wk δ)} .snd t∈w) (snd (lookup wk δ)))
      , (∈∈ₛ {a = t} {b = fst (lookup wk δ)} .snd t∈w
        , ∈∈ₛ {a = v} {b = t} .snd v∈t)

  unionEq-out : {n : ℕ} (ck wk : Fin n) (δ : Vec DefC.SM n)
              → ⟨ δ DefC.⊨ᵐ unionEq ck wk ⟩
              → fst (lookup ck δ) ≡ ⋃ (fst (lookup wk δ))
  unionEq-out ck wk δ h = eqFrame-out ck (unionMem wk) δ
    (⋃ (fst (lookup wk δ)))
    (λ v k → unionSub (fst (lookup wk δ)) v (snd (lookup wk δ)) k)
    (λ v v∈ k → unionMem-out wk δ v v∈ k)
    (λ v v∈ k → unionMem-in wk δ v v∈ k) h

  unionEq-in : {n : ℕ} (ck wk : Fin n) (δ : Vec DefC.SM n)
             → fst (lookup ck δ) ≡ ⋃ (fst (lookup wk δ))
             → ⟨ δ DefC.⊨ᵐ unionEq ck wk ⟩
  unionEq-in ck wk δ e = eqFrame-in ck (unionMem wk) δ
    (⋃ (fst (lookup wk δ)))
    (λ v k → unionSub (fst (lookup wk δ)) v (snd (lookup wk δ)) k)
    (λ v v∈ k → unionMem-out wk δ v v∈ k)
    (λ v v∈ k → unionMem-in wk δ v v∈ k) e

  capF-out : {n : ℕ} (bk ck : Fin n) (δ : Vec DefC.SM n)
           → ⟨ δ DefC.⊨ᵐ capF bk ck ⟩
           → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
  capF-out bk ck δ (h₁ , h₂) =
    PT.rec (snd (fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)))) go h₁
    where
    all : (v : S) → ⟨ v ∈ˢ fst (lookup bk δ) ⟩ → ⟨ fst (lookup ck δ) ∈ˢ v ⟩
    all v v∈ = h₂ (pt v (entry∈ bk δ v v∈)) v∈
    go : Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ fst (lookup bk δ))
           ⊓ ((wm ∷ δ) DefC.⊨ᵐ unionEq (suc ck) f0) ⟩
       → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
    go (wm , (w∈b , e)) = cap-in (fst (lookup bk δ)) (fst (lookup ck δ))
      (fst wm) w∈b (unionEq-out (suc ck) f0 (wm ∷ δ) e) all

  capF-in : {n : ℕ} (bk ck : Fin n) (δ : Vec DefC.SM n)
          → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
          → ⟨ δ DefC.⊨ᵐ capF bk ck ⟩
  capF-in bk ck δ h = (part₁ , part₂)
    where
    part₁ : ⟨ δ DefC.⊨ᵐ (∃̇∈ (var bk) (unionEq (suc ck) f0)) ⟩
    part₁ = PT.map go (cap-out (fst (lookup bk δ)) (fst (lookup ck δ)) h)
      where
      go : Σ[ w ∈ S ] (⟨ w ∈ˢ fst (lookup bk δ) ⟩ × (fst (lookup ck δ) ≡ ⋃ w))
         → Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ fst (lookup bk δ))
             ⊓ ((wm ∷ δ) DefC.⊨ᵐ unionEq (suc ck) f0) ⟩
      go (w , (w∈b , e)) = pt w (entry∈ bk δ w w∈b)
        , (w∈b , unionEq-in (suc ck) f0 (pt w (entry∈ bk δ w w∈b) ∷ δ) e)
    part₂ : (wm : DefC.SM) → ⟨ fst wm ∈ˢ fst (lookup bk δ) ⟩
          → ⟨ fst (lookup ck δ) ∈ˢ fst wm ⟩
    part₂ wm w∈ = cap-all (fst (lookup bk δ)) (fst (lookup ck δ)) h (fst wm) w∈

  leftMem-out : {n : ℕ} (bk : Fin n) (δ : Vec DefC.SM n) (v : S)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ leftMem bk ⟩
              → ⟨ v ∈ˢ left (fst (lookup bk δ)) ⟩
  leftMem-out bk δ v v∈ h =
    ∈∈ₛ {a = v} {b = ⋃ (⋂ (fst (lookup bk δ)))} .snd
      (union-ax (⋂ (fst (lookup bk δ))) v .snd (PT.map go h))
    where
    go : Σ[ cm ∈ DefC.SM ]
           ⟨ ((cm ∷ pt v v∈ ∷ δ) DefC.⊨ᵐ capF (suc (suc bk)) f0)
             ⊓ (v ∈ˢ fst cm) ⟩
       → Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ (fst (lookup bk δ)) ⟩ × ⟨ v ∈ₛ t ⟩)
    go (cm , (hc , v∈c)) = fst cm
      , (∈∈ₛ {a = fst cm} {b = ⋂ (fst (lookup bk δ))} .fst
          (capF-out (suc (suc bk)) f0 (cm ∷ pt v v∈ ∷ δ) hc)
        , ∈∈ₛ {a = v} {b = fst cm} .fst v∈c)

  leftMem-in : {n : ℕ} (bk : Fin n) (δ : Vec DefC.SM n) (v : S)
               (v∈ : ⟨ v ∈ˢ C ⟩)
             → ⟨ v ∈ˢ left (fst (lookup bk δ)) ⟩
             → ⟨ (pt v v∈ ∷ δ) DefC.⊨ᵐ leftMem bk ⟩
  leftMem-in bk δ v v∈ h = PT.map go
    (union-ax (⋂ (fst (lookup bk δ))) v .fst
      (∈∈ₛ {a = v} {b = ⋃ (⋂ (fst (lookup bk δ)))} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ (fst (lookup bk δ)) ⟩ × ⟨ v ∈ₛ t ⟩)
       → Σ[ cm ∈ DefC.SM ]
           ⟨ ((cm ∷ pt v v∈ ∷ δ) DefC.⊨ᵐ capF (suc (suc bk)) f0)
             ⊓ (v ∈ˢ fst cm) ⟩
    go (t , (t∈⋂ , v∈t)) = pt t t∈C
      , (capF-in (suc (suc bk)) f0 (pt t t∈C ∷ pt v v∈ ∷ δ)
          (∈∈ₛ {a = t} {b = ⋂ (fst (lookup bk δ))} .snd t∈⋂)
        , ∈∈ₛ {a = v} {b = t} .snd v∈t)
      where
      t∈C : ⟨ t ∈ˢ C ⟩
      t∈C = cap∈ (fst (lookup bk δ)) t (snd (lookup bk δ))
        (∈∈ₛ {a = t} {b = ⋂ (fst (lookup bk δ))} .snd t∈⋂)

  leftSub : (b v : S) → ⟨ b ∈ˢ C ⟩ → ⟨ v ∈ˢ left b ⟩ → ⟨ v ∈ˢ C ⟩
  leftSub b v b∈ h = PT.rec (snd (v ∈ˢ C)) go
    (union-ax (⋂ b) v .fst (∈∈ₛ {a = v} {b = ⋃ (⋂ b)} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ b ⟩ × ⟨ v ∈ₛ t ⟩) → ⟨ v ∈ˢ C ⟩
    go (t , (t∈⋂ , v∈t)) = mem t v (∈∈ₛ {a = v} {b = t} .snd v∈t)
      (cap∈ b t b∈ (∈∈ₛ {a = t} {b = ⋂ b} .snd t∈⋂))

  leftEqF-out : {n : ℕ} (lk bk : Fin n) (δ : Vec DefC.SM n)
              → ⟨ δ DefC.⊨ᵐ leftEqF lk bk ⟩
              → fst (lookup lk δ) ≡ left (fst (lookup bk δ))
  leftEqF-out lk bk δ h = eqFrame-out lk (leftMem bk) δ
    (left (fst (lookup bk δ)))
    (λ v k → leftSub (fst (lookup bk δ)) v (snd (lookup bk δ)) k)
    (λ v v∈ k → leftMem-out bk δ v v∈ k)
    (λ v v∈ k → leftMem-in bk δ v v∈ k) h

  leftEqF-in : {n : ℕ} (lk bk : Fin n) (δ : Vec DefC.SM n)
             → fst (lookup lk δ) ≡ left (fst (lookup bk δ))
             → ⟨ δ DefC.⊨ᵐ leftEqF lk bk ⟩
  leftEqF-in lk bk δ e = eqFrame-in lk (leftMem bk) δ
    (left (fst (lookup bk δ)))
    (λ v k → leftSub (fst (lookup bk δ)) v (snd (lookup bk δ)) k)
    (λ v v∈ k → leftMem-out bk δ v v∈ k)
    (λ v v∈ k → leftMem-in bk δ v v∈ k) e
```

<!--en-->
The right projection is the empty set off a pair, which the operations layer
reads separately, so its description keeps one case split; the split is faithful
because a pair inside the carrier has both components inside the carrier, so a
decomposition anywhere is a decomposition here.
<!--zh-->
右投影在非对上取空集，运算层为此另有读引理，故其描述保留一次情形分裂；该分裂忠实，因为载体内的一个对，两个分量都在载体内，故任何地方的分解都是此处的分解。
<!--/-->

```agda
  isPairF-in : {n : ℕ} (bk : Fin n) (δ : Vec DefC.SM n) (p q : S)
             → fst (lookup bk δ) ≡ pr p q → ⟨ δ DefC.⊨ᵐ isPairF bk ⟩
  isPairF-in bk δ p q e = ∣ pt p p∈C , ∣ pt q q∈C
    , prAt-in (suc (suc bk)) f1 f0 (pt q q∈C ∷ pt p p∈C ∷ δ) e ∣₁ ∣₁
    where
    pr∈C : ⟨ pr p q ∈ˢ C ⟩
    pr∈C = subst (λ t → ⟨ t ∈ˢ C ⟩) e (snd (lookup bk δ))
    p∈C : ⟨ p ∈ˢ C ⟩
    p∈C = prL∈ p q pr∈C
    q∈C : ⟨ q ∈ˢ C ⟩
    q∈C = prR∈ p q pr∈C

  isPairF-out : {n : ℕ} (bk : Fin n) (δ : Vec DefC.SM n)
              → ⟨ δ DefC.⊨ᵐ isPairF bk ⟩ → ⟨ isPair (fst (lookup bk δ)) ⟩
  isPairF-out bk δ h = PT.rec (snd (isPair (fst (lookup bk δ)))) k0 h
    where
    k0 : Σ[ pm ∈ DefC.SM ] ⟨ (pm ∷ δ) DefC.⊨ᵐ (∃̇ (prAt (suc (suc bk)) f1 f0)) ⟩
       → ⟨ isPair (fst (lookup bk δ)) ⟩
    k0 (pm , h1) = PT.map k1 h1
      where
      k1 : Σ[ qm ∈ DefC.SM ]
             ⟨ (qm ∷ pm ∷ δ) DefC.⊨ᵐ prAt (suc (suc bk)) f1 f0 ⟩
         → Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ fst (lookup bk δ) ≡ₕ pr p q ⟩
      k1 (qm , e) = fst pm , (fst qm
        , prAt-out (suc (suc bk)) f1 f0 (qm ∷ pm ∷ δ) e)

  rightEqF-out : {n : ℕ} (rk bk : Fin n) (δ : Vec DefC.SM n)
               → ⟨ δ DefC.⊨ᵐ rightEqF rk bk ⟩
               → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
  rightEqF-out rk bk δ h = PT.rec
    (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) branch h
    where
    atPair : Σ[ pm ∈ DefC.SM ]
               ⟨ (pm ∷ δ) DefC.⊨ᵐ (∃̇ (prAt (suc (suc bk)) f1 f0
                   ∧̇ (var (suc (suc rk)) ≐ var f0))) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    atPair (pm , h1) = PT.rec
      (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) k1 h1
      where
      k1 : Σ[ qm ∈ DefC.SM ]
             ⟨ ((qm ∷ pm ∷ δ) DefC.⊨ᵐ prAt (suc (suc bk)) f1 f0)
               ⊓ (fst (lookup rk δ) ≡ₕ fst qm) ⟩
         → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
      k1 (qm , (e , r≡q)) = r≡q ∙ sym
        (right-at-pair (fst (lookup bk δ)) (fst pm) (fst qm) b≡)
        where
        b≡ : fst (lookup bk δ) ≡ pr (fst pm) (fst qm)
        b≡ = prAt-out (suc (suc bk)) f1 f0 (qm ∷ pm ∷ δ) e
    noPair : ⟨ ((¬ (δ DefC.⊨ᵐ isPairF bk))
             ⊓ (δ DefC.⊨ᵐ (∀̇∈ (var rk) ⊥̇))) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    noPair (nb , empty) = r≡∅ ∙ sym right≡∅
      where
      r≡∅ : fst (lookup rk δ) ≡ ∅
      r≡∅ = empty-⊆ (fst (lookup rk δ))
        (λ x h' → Empty.rec* (empty (pt x (entry∈ rk δ x h')) h'))
      right≡∅ : right (fst (lookup bk δ)) ≡ ∅
      right≡∅ = right-nonpair (fst (lookup bk δ))
        (λ p q e → nb (isPairF-in bk δ p q e))
    branch : ⟨ δ DefC.⊨ᵐ (∃̇ (∃̇ (prAt (suc (suc bk)) f1 f0
               ∧̇ (var (suc (suc rk)) ≐ var f0)))) ⟩
           ⊎ ⟨ (¬ (δ DefC.⊨ᵐ isPairF bk))
               ⊓ (δ DefC.⊨ᵐ (∀̇∈ (var rk) ⊥̇)) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    branch (inl h1) = PT.rec
      (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) atPair h1
    branch (inr h1) = noPair h1

  rightEqF-in : {n : ℕ} (rk bk : Fin n) (δ : Vec DefC.SM n)
              → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
              → ⟨ δ DefC.⊨ᵐ rightEqF rk bk ⟩
  rightEqF-in rk bk δ e = go (lem (isPair (fst (lookup bk δ))))
    where
    go : ⟨ isPair (fst (lookup bk δ)) ⟩
       ⊎ (⟨ isPair (fst (lookup bk δ)) ⟩ → Empty.⊥)
       → ⟨ δ DefC.⊨ᵐ rightEqF rk bk ⟩
    go (inl h) = PT.rec (snd (δ DefC.⊨ᵐ rightEqF rk bk)) k h
      where
      k : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ fst (lookup bk δ) ≡ₕ pr p q ⟩
        → ⟨ δ DefC.⊨ᵐ rightEqF rk bk ⟩
      k (p , q , b≡) = ∣ inl ∣ pt p p∈C , ∣ pt q q∈C
        , (prAt-in (suc (suc bk)) f1 f0 (pt q q∈C ∷ pt p p∈C ∷ δ) b≡
          , e ∙ right≡q) ∣₁ ∣₁ ∣₁
        where
        pr∈C : ⟨ pr p q ∈ˢ C ⟩
        pr∈C = subst (λ t → ⟨ t ∈ˢ C ⟩) b≡ (snd (lookup bk δ))
        p∈C : ⟨ p ∈ˢ C ⟩
        p∈C = prL∈ p q pr∈C
        q∈C : ⟨ q ∈ˢ C ⟩
        q∈C = prR∈ p q pr∈C
        right≡q : right (fst (lookup bk δ)) ≡ q
        right≡q = right-at-pair (fst (lookup bk δ)) p q b≡
    go (inr nb) = ∣ inr (nb' , empty) ∣₁
      where
      nb' : ⟨ δ DefC.⊨ᵐ isPairF bk ⟩ → Empty.⊥
      nb' k = nb (isPairF-out bk δ k)
      right≡∅ : right (fst (lookup bk δ)) ≡ ∅
      right≡∅ = right-nonpair (fst (lookup bk δ))
        (λ p q k → nb ∣ p , (q , k) ∣₁)
      empty : (xm : DefC.SM) → ⟨ fst xm ∈ˢ fst (lookup rk δ) ⟩ → ⟨ ⊥ ⟩
      empty xm k = Empty.rec (∅-empty (fst xm)
        (∈∈ₛ {a = fst xm} {b = ∅} .fst
          (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (e ∙ right≡∅) k)))
```

```agda
module Slot (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C))
            (mA : ⟪ C ⟫) (qA : ⟪ C ⟫↪ mA ≡ A) (∅∈C : ⟨ ∅ ∈ˢ C ⟩) where

  open Reads C Ctr
  open Desc C Ctr
  open Frames C Ctr

  tuple3L4 tuple4L4 : Formula ⟪ C ⟫ 9
  tuple3L4 = prAt f4 f3 f2 ∧̇ (prAt f0 f1 f2 ∧̇ prAt f5 f3 f0)
  tuple4L4 = prAt f4 f3 f2 ∧̇ (prAt f0 f2 f1 ∧̇ prAt f5 f3 f0)

  tuple3L3 tuple4L3 : Formula ⟪ C ⟫ 8
  tuple3L3 = ∃̇ tuple3L4
  tuple4L3 = ∃̇ tuple4L4

  tuple3L2 tuple4L2 : Formula ⟪ C ⟫ 7
  tuple3L2 = ∃̇∈ (var f5) tuple3L3
  tuple4L2 = ∃̇∈ (var f5) tuple4L3

  tuple3L1 tuple4L1 : Formula ⟪ C ⟫ 6
  tuple3L1 = ∃̇ tuple3L2
  tuple4L1 = ∃̇ tuple4L2

  tuple3L0 tuple4L0 : Formula ⟪ C ⟫ 5
  tuple3L0 = ∃̇ tuple3L1
  tuple4L0 = ∃̇ tuple4L1

  sliceMem : Formula ⟪ C ⟫ 6
  sliceMem = ∃̇ (prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f5))

  shape11 shape12 shape13 shape14 : Formula ⟪ C ⟫ 6
  shape11 = sglAt f2 f1 ∨̇ (∃̇ (prAt f0 f5 f1 ∧̇ pairAt f3 f2 f0))
  shape12 = sglAt f2 f1 ∨̇ (∃̇ (prAt f0 f1 f5 ∧̇ pairAt f3 f2 f0))
  shape13 = (var f2 ≐ var f1) ∨̇ prAt f2 f0 f4
  shape14 = (var f2 ≐ var f1) ∨̇ prAt f2 f4 f0

  mem0 mem1 mem2 mem3 mem4 mem5 mem6 mem7 : Formula ⟪ C ⟫ 4
  mem8 mem9 mem10 mem11 mem12 mem13 mem14 mem15 : Formula ⟪ C ⟫ 4
  mem0 = (var f0 ≐ var f2) ∨̇ (var f0 ≐ var f1)
  mem1 = (var f0 ∈̇ var f2) ∧̇ (¬̇ (var f0 ∈̇ var f1))
  mem2 = ∃̇∈ (var f2) (∃̇∈ (var f2) (prAt f2 f1 f0))
  mem3 = ∃̇∈ (var f1) tuple3L0
  mem4 = ∃̇∈ (var f1) tuple4L0
  mem5 = ∃̇∈ (var f2) (var f1 ∈̇ var f0)
  mem6 = ∃̇∈ (var f2) (∃̇ (prAt f1 f2 f0))
  mem7 = ∃̇∈ (var f2) (∃̇∈ (var f3) ((var f1 ∈̇ var f0) ∧̇ prAt f2 f1 f0))
  mem8 = ∃̇∈ (var f1) (eqFrame f1 sliceMem)
  mem9 = sglAt f0 f2 ∨̇ pairAt f0 f2 f1
  mem10 = ∃̇ (prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f3))
  mem11 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape11)))
  mem12 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape12)))
  mem13 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape13)))
  mem14 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape14)))
  mem15 = (var f0 ∈̇ var f2) ∧̇ (var f0 ∈̇ con mA)
```

<!--en-->
The adequacy of the twelve operations whose value is read without the
projections. Each is the operations chapter's read in one direction and its
write in the other, with the quantifier witnesses placed in the carrier by
transitivity.
<!--zh-->
其值无须投影即可读出的十二个运算的适足性。每条都是运算章的读引理走一个方向、写引理走另一个方向，而量词的见证由传递性安放进载体。
<!--/-->

```agda
  mem0-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem0 ⟩
           → ⟨ z ∈ˢ Fof op0 a b ⟩
  mem0-out z b a y z∈ b∈ a∈ y∈ h =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f0 a b)) (F0-spec a b z .snd h)

  mem0-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op0 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem0 ⟩
  mem0-in z b a y z∈ b∈ a∈ y∈ h =
    F0-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f0 a b) h)

  mem1-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem1 ⟩
           → ⟨ z ∈ˢ Fof op1 a b ⟩
  mem1-out z b a y z∈ b∈ a∈ y∈ h =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f1 a b)) (F1-spec a b z .snd h)

  mem1-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op1 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem1 ⟩
  mem1-in z b a y z∈ b∈ a∈ y∈ h =
    F1-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f1 a b) h)

  mem2-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem2 ⟩
           → ⟨ z ∈ˢ Fof op2 a b ⟩
  mem2-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f2 a b))
    (F2-write a b z (PT.rec squash₁ outer h))
    where
    outer : Σ[ pm ∈ DefC.SM ] ⟨ (fst pm ∈ˢ a)
              ⊓ ((pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                 DefC.⊨ᵐ (∃̇∈ (var f2) (prAt f2 f1 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩) ∥₁
    outer (pm , (p∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ qm ∈ DefC.SM ] ⟨ (fst qm ∈ˢ b)
                ⊓ ((qm ∷ pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                   DefC.⊨ᵐ prAt f2 f1 f0) ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩)
      inner (qm , (q∈b , e)) = fst pm , (fst qm , (p∈a , (q∈b ,
        prAt-out f2 f1 f0
          (qm ∷ pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e)))

  mem2-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op2 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem2 ⟩
  mem2-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem2)) go
    (F2-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f2 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem2 ⟩
    go (p , q , p∈a , q∈b , e) =
      ∣ pt p (mem a p p∈a a∈)
      , (p∈a , ∣ pt q (mem b q q∈b b∈)
        , (q∈b , prAt-in f2 f1 f0
            (pt q (mem b q q∈b b∈) ∷ pt p (mem a p p∈a a∈)
             ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) ∣₁) ∣₁

  mem5-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem5 ⟩
           → ⟨ z ∈ˢ Fof op5 a b ⟩
  mem5-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f5 a b))
    (F5-spec a b z .snd (PT.map go h))
    where
    go : Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ a) ⊓ (z ∈ˢ fst wm) ⟩
       → Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (z ∈ˢ w) ⟩
    go (wm , k) = fst wm , k

  mem5-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op5 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem5 ⟩
  mem5-in z b a y z∈ b∈ a∈ y∈ h = PT.map go
    (F5-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f5 a b) h))
    where
    go : Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (z ∈ˢ w) ⟩
       → Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ a) ⊓ (z ∈ˢ fst wm) ⟩
    go (w , (w∈a , z∈w)) = pt w (mem a w w∈a a∈) , (w∈a , z∈w)

  mem6-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem6 ⟩
           → ⟨ z ∈ˢ Fof op6 a b ⟩
  mem6-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f6 a b))
    (F6-write a b z (PT.rec squash₁ outer h))
    where
    outer : Σ[ sm ∈ DefC.SM ] ⟨ (fst sm ∈ˢ a)
              ⊓ ((sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                 DefC.⊨ᵐ (∃̇ (prAt f1 f2 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩) ∥₁
    outer (sm , (s∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ vm ∈ DefC.SM ]
                ⟨ (vm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                  DefC.⊨ᵐ prAt f1 f2 f0 ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩)
      inner (vm , e) = z , (fst vm
        , (subst (λ w → ⟨ w ∈ˢ a ⟩)
            (prAt-out f1 f2 f0
              (vm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) s∈a
          , refl))

  mem6-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op6 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem6 ⟩
  mem6-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem6)) go
    (F6-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f6 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem6 ⟩
    go (p , q , pq∈a , e) =
      ∣ pt (pr z q) s∈C , (s∈a , ∣ pt q q∈C
        , prAt-in f1 f2 f0
            (pt q q∈C ∷ pt (pr z q) s∈C
             ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) refl ∣₁) ∣₁
      where
      s∈a : ⟨ pr z q ∈ˢ a ⟩
      s∈a = subst (λ w → ⟨ pr w q ∈ˢ a ⟩) (sym e) pq∈a
      s∈C : ⟨ pr z q ∈ˢ C ⟩
      s∈C = mem a (pr z q) s∈a a∈
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = prR∈ z q s∈C

  mem7-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem7 ⟩
           → ⟨ z ∈ˢ Fof op7 a b ⟩
  mem7-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f7 a b))
    (F7-write a b z (PT.rec squash₁ outer h))
    where
    outer : Σ[ pm ∈ DefC.SM ] ⟨ (fst pm ∈ˢ a)
              ⊓ ((pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                 DefC.⊨ᵐ (∃̇∈ (var f3) ((var f1 ∈̇ var f0) ∧̇ prAt f2 f1 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩) ∥₁
    outer (pm , (p∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ qm ∈ DefC.SM ] ⟨ (fst qm ∈ˢ a)
                ⊓ ((qm ∷ pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                   DefC.⊨ᵐ ((var f1 ∈̇ var f0) ∧̇ prAt f2 f1 f0)) ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩)
      inner (qm , (q∈a , (p∈q , e))) = fst pm , (fst qm , (p∈a , (q∈a , (p∈q ,
        prAt-out f2 f1 f0
          (qm ∷ pm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e))))

  mem7-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op7 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem7 ⟩
  mem7-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem7)) go
    (F7-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f7 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ]
           (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem7 ⟩
    go (p , q , p∈a , q∈a , p∈q , e) =
      ∣ pt p (mem a p p∈a a∈)
      , (p∈a , ∣ pt q (mem a q q∈a a∈)
        , (q∈a , (p∈q , prAt-in f2 f1 f0
            (pt q (mem a q q∈a a∈) ∷ pt p (mem a p p∈a a∈)
             ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e)) ∣₁) ∣₁

  mem9-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem9 ⟩
           → ⟨ z ∈ˢ Fof op9 a b ⟩
  mem9-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f9 a b))
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) z .snd (PT.map go h))
    where
    go : ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ sglAt f0 f2 ⟩
       ⊎ ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ pairAt f0 f2 f1 ⟩
       → (z ≡ ⁅ a ⁆s) ⊎ (z ≡ ⁅ a , b ⁆)
    go (inl s) = inl
      (sglAt-out f0 f2 (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) s)
    go (inr s) = inr
      (pairAt-out f0 f2 f1 (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) s)

  mem9-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op9 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem9 ⟩
  mem9-in z b a y z∈ b∈ a∈ y∈ h = PT.map go
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f9 a b) h))
    where
    go : (z ≡ ⁅ a ⁆s) ⊎ (z ≡ ⁅ a , b ⁆)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ sglAt f0 f2 ⟩
       ⊎ ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ pairAt f0 f2 f1 ⟩
    go (inl e) = inl
      (sglAt-in f0 f2 (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e)
    go (inr e) = inr
      (pairAt-in f0 f2 f1 (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e)

  mem10-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem10 ⟩
            → ⟨ z ∈ˢ Fof op10 a b ⟩
  mem10-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f10 a b))
    (PT.rec (snd (z ∈ˢ F10 a b)) go h)
    where
    go : Σ[ sm ∈ DefC.SM ]
           ⟨ (sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ (prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f3)) ⟩
       → ⟨ z ∈ˢ F10 a b ⟩
    go (sm , (e , s∈a)) = subst ⟨_⟩ (sym (F10-spec a b z))
      (subst (λ w → ⟨ w ∈ˢ a ⟩)
        (prAt-out f0 f2 f1
          (sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) s∈a)

  mem10-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op10 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem10 ⟩
  mem10-in z b a y z∈ b∈ a∈ y∈ h =
    ∣ pt (pr b z) s∈C , (prAt-in f0 f2 f1
        (pt (pr b z) s∈C ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) refl
      , s∈a) ∣₁
    where
    s∈a : ⟨ pr b z ∈ˢ a ⟩
    s∈a = subst ⟨_⟩ (F10-spec a b z)
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f10 a b) h)
    s∈C : ⟨ pr b z ∈ˢ C ⟩
    s∈C = mem a (pr b z) s∈a a∈

  mem15-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem15 ⟩
            → ⟨ z ∈ˢ Fof op15 a b ⟩
  mem15-out z b a y z∈ b∈ a∈ y∈ (z∈a , z∈mA) =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f15 a b))
      (subst ⟨_⟩ (sym (F15C.F15-spec a z))
        (z∈a , subst (λ w → ⟨ z ∈ˢ w ⟩) qA z∈mA))
    where
    module F15C = F15Of A

  mem15-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op15 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem15 ⟩
  mem15-in z b a y z∈ b∈ a∈ y∈ h =
    (parts .fst , subst (λ w → ⟨ z ∈ˢ w ⟩) (sym qA) (parts .snd))
    where
    module F15C = F15Of A
    parts : ⟨ (z ∈ˢ a) ⊓ (z ∈ˢ A) ⟩
    parts = subst ⟨_⟩ (F15C.F15-spec a z)
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f15 a b) h)
```

<!--en-->
The two tuple insertions read five witnesses each: the pair drawn from the second
argument, its two components, the member of the first argument, and the inner
tuple. Every witness is a member of the carrier, three of them by the pair
reading and one by the value's own membership. The image collection reads one
witness and one equality frame: the value is the slice of the first argument at a
member of the second, and a slice is a subset of the carrier whenever the
argument is a member of it.
<!--zh-->
两个三元组插入各读出五个见证：取自第二实参的那个对、它的两个分量、第一实参的成员，以及内层三元组。每个见证都是载体的成员，其中三个由对读式给出，一个由该值自身的隶属给出。像的收集读出一个见证与一个等词框架：该值是第一实参在第二实参某成员处的切片，而只要实参是载体的成员，切片就是载体的子集。
<!--/-->

```agda
  mem3-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem3 ⟩
           → ⟨ z ∈ˢ Fof op3 a b ⟩
  mem3-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f3 a b))
    (F3-write a b z (PT.rec squash₁ k0 h))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
             (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩) ∥₁
    k0 : Σ[ sm ∈ DefC.SM ] ⟨ (fst sm ∈ˢ b)
           ⊓ ((sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
              DefC.⊨ᵐ tuple3L0) ⟩
       → Goal
    k0 (sm , (s∈b , h1)) = PT.rec squash₁ k1 h1
      where
      k1 : Σ[ pm ∈ DefC.SM ]
             ⟨ (pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
               DefC.⊨ᵐ tuple3L1 ⟩
         → Goal
      k1 (pm , h2) = PT.rec squash₁ k2 h2
        where
        k2 : Σ[ qm ∈ DefC.SM ]
               ⟨ (qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                 DefC.⊨ᵐ tuple3L2 ⟩
           → Goal
        k2 (qm , h3) = PT.rec squash₁ k3 h3
          where
          k3 : Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ a)
                 ⊓ ((wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                     ∷ pt y y∈ ∷ []) DefC.⊨ᵐ tuple3L3) ⟩
             → Goal
          k3 (wm , (w∈a , h4)) = PT.map k4 h4
            where
            k4 : Σ[ tm ∈ DefC.SM ]
                   ⟨ (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                      ∷ pt y y∈ ∷ []) DefC.⊨ᵐ tuple3L4 ⟩
               → Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
                   (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩)
            k4 (tm , (e1 , (e2 , e3))) =
              fst pm , (fst wm , (fst qm , (w∈a , (pq∈b , zeq))))
              where
              pq∈b : ⟨ pr (fst pm) (fst qm) ∈ˢ b ⟩
              pq∈b = subst (λ v → ⟨ v ∈ˢ b ⟩)
                (prAt-out f4 f3 f2
                  (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e1) s∈b
              zeq : z ≡ pr (fst pm) (pr (fst wm) (fst qm))
              zeq = prAt-out f5 f3 f0
                (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                 ∷ pt y y∈ ∷ []) e3
                ∙ cong (pr (fst pm)) (prAt-out f0 f1 f2
                    (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                     ∷ pt y y∈ ∷ []) e2)

  mem3-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op3 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem3 ⟩
  mem3-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem3)) go
    (F3-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f3 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
           (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem3 ⟩
    go (p , w , q , w∈a , pq∈b , e) =
      ∣ pt (pr p q) s∈C , (pq∈b , ∣ pt p p∈C , ∣ pt q q∈C
        , ∣ pt w (mem a w w∈a a∈) , (w∈a , ∣ pt (pr w q) t∈C
          , (prAt-in f4 f3 f2 env₉ refl
            , (prAt-in f0 f1 f2 env₉ refl , prAt-in f5 f3 f0 env₉ e)) ∣₁) ∣₁ ∣₁ ∣₁) ∣₁
      where
      s∈C : ⟨ pr p q ∈ˢ C ⟩
      s∈C = mem b (pr p q) pq∈b b∈
      p∈C : ⟨ p ∈ˢ C ⟩
      p∈C = prL∈ p q s∈C
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = prR∈ p q s∈C
      t∈C : ⟨ pr w q ∈ˢ C ⟩
      t∈C = prR∈ p (pr w q) (subst (λ v → ⟨ v ∈ˢ C ⟩) e z∈)
      env₉ : Vec DefC.SM 9
      env₉ = pt (pr w q) t∈C ∷ pt w (mem a w w∈a a∈) ∷ pt q q∈C ∷ pt p p∈C
           ∷ pt (pr p q) s∈C ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []

  mem4-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem4 ⟩
           → ⟨ z ∈ˢ Fof op4 a b ⟩
  mem4-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f4 a b))
    (F4-write a b z (PT.rec squash₁ k0 h))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
             (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩) ∥₁
    k0 : Σ[ sm ∈ DefC.SM ] ⟨ (fst sm ∈ˢ b)
           ⊓ ((sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
              DefC.⊨ᵐ tuple4L0) ⟩
       → Goal
    k0 (sm , (s∈b , h1)) = PT.rec squash₁ k1 h1
      where
      k1 : Σ[ pm ∈ DefC.SM ]
             ⟨ (pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
               DefC.⊨ᵐ tuple4L1 ⟩
         → Goal
      k1 (pm , h2) = PT.rec squash₁ k2 h2
        where
        k2 : Σ[ qm ∈ DefC.SM ]
               ⟨ (qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                 DefC.⊨ᵐ tuple4L2 ⟩
           → Goal
        k2 (qm , h3) = PT.rec squash₁ k3 h3
          where
          k3 : Σ[ wm ∈ DefC.SM ] ⟨ (fst wm ∈ˢ a)
                 ⊓ ((wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                     ∷ pt y y∈ ∷ []) DefC.⊨ᵐ tuple4L3) ⟩
             → Goal
          k3 (wm , (w∈a , h4)) = PT.map k4 h4
            where
            k4 : Σ[ tm ∈ DefC.SM ]
                   ⟨ (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                      ∷ pt y y∈ ∷ []) DefC.⊨ᵐ tuple4L4 ⟩
               → Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
                   (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩)
            k4 (tm , (e1 , (e2 , e3))) =
              fst pm , (fst qm , (fst wm , (w∈a , (pq∈b , zeq))))
              where
              pq∈b : ⟨ pr (fst pm) (fst qm) ∈ˢ b ⟩
              pq∈b = subst (λ v → ⟨ v ∈ˢ b ⟩)
                (prAt-out f4 f3 f2
                  (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e1) s∈b
              zeq : z ≡ pr (fst pm) (pr (fst qm) (fst wm))
              zeq = prAt-out f5 f3 f0
                (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                 ∷ pt y y∈ ∷ []) e3
                ∙ cong (pr (fst pm)) (prAt-out f0 f2 f1
                    (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                     ∷ pt y y∈ ∷ []) e2)

  mem4-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op4 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem4 ⟩
  mem4-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem4)) go
    (F4-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f4 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
           (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem4 ⟩
    go (p , q , w , w∈a , pq∈b , e) =
      ∣ pt (pr p q) s∈C , (pq∈b , ∣ pt p p∈C , ∣ pt q q∈C
        , ∣ pt w (mem a w w∈a a∈) , (w∈a , ∣ pt (pr q w) t∈C
          , (prAt-in f4 f3 f2 env₉ refl
            , (prAt-in f0 f2 f1 env₉ refl , prAt-in f5 f3 f0 env₉ e)) ∣₁) ∣₁ ∣₁ ∣₁) ∣₁
      where
      s∈C : ⟨ pr p q ∈ˢ C ⟩
      s∈C = mem b (pr p q) pq∈b b∈
      p∈C : ⟨ p ∈ˢ C ⟩
      p∈C = prL∈ p q s∈C
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = prR∈ p q s∈C
      t∈C : ⟨ pr q w ∈ˢ C ⟩
      t∈C = prR∈ p (pr q w) (subst (λ v → ⟨ v ∈ˢ C ⟩) e z∈)
      env₉ : Vec DefC.SM 9
      env₉ = pt (pr q w) t∈C ∷ pt w (mem a w w∈a a∈) ∷ pt q q∈C ∷ pt p p∈C
           ∷ pt (pr p q) s∈C ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []
```

```agda
  sliceMem-out : (z b a y c v : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
                 (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩) (c∈ : ⟨ c ∈ˢ C ⟩)
                 (v∈ : ⟨ v ∈ˢ C ⟩)
               → ⟨ (pt v v∈ ∷ pt c c∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                    ∷ pt y y∈ ∷ []) DefC.⊨ᵐ sliceMem ⟩
               → ⟨ v ∈ˢ F10 a c ⟩
  sliceMem-out z b a y c v z∈ b∈ a∈ y∈ c∈ v∈ h =
    PT.rec (snd (v ∈ˢ F10 a c)) go h
    where
    go : Σ[ sm ∈ DefC.SM ]
           ⟨ ((sm ∷ pt v v∈ ∷ pt c c∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
               ∷ pt y y∈ ∷ []) DefC.⊨ᵐ prAt f0 f2 f1) ⊓ (fst sm ∈ˢ a) ⟩
       → ⟨ v ∈ˢ F10 a c ⟩
    go (sm , (e , s∈a)) = subst ⟨_⟩ (sym (F10-spec a c v))
      (subst (λ w → ⟨ w ∈ˢ a ⟩)
        (prAt-out f0 f2 f1
          (sm ∷ pt v v∈ ∷ pt c c∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
           ∷ pt y y∈ ∷ []) e) s∈a)

  sliceMem-in : (z b a y c v : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
                (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩) (c∈ : ⟨ c ∈ˢ C ⟩)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ v ∈ˢ F10 a c ⟩
              → ⟨ (pt v v∈ ∷ pt c c∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) DefC.⊨ᵐ sliceMem ⟩
  sliceMem-in z b a y c v z∈ b∈ a∈ y∈ c∈ v∈ h =
    ∣ pt (pr c v) s∈C
    , (prAt-in f0 f2 f1
        (pt (pr c v) s∈C ∷ pt v v∈ ∷ pt c c∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
         ∷ pt y y∈ ∷ []) refl
      , s∈a) ∣₁
    where
    s∈a : ⟨ pr c v ∈ˢ a ⟩
    s∈a = subst ⟨_⟩ (F10-spec a c v) h
    s∈C : ⟨ pr c v ∈ˢ C ⟩
    s∈C = mem a (pr c v) s∈a a∈

  sliceSub : (a c : S) → ⟨ a ∈ˢ C ⟩ → (v : S) → ⟨ v ∈ˢ F10 a c ⟩ → ⟨ v ∈ˢ C ⟩
  sliceSub a c a∈ v h = prR∈ c v (mem a (pr c v) (subst ⟨_⟩ (F10-spec a c v) h) a∈)

  mem8-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem8 ⟩
           → ⟨ z ∈ˢ Fof op8 a b ⟩
  mem8-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f8 a b))
    (PT.rec (snd (z ∈ˢ F8 a b)) go h)
    where
    go : Σ[ cm ∈ DefC.SM ] ⟨ (fst cm ∈ˢ b)
           ⊓ ((cm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
              DefC.⊨ᵐ eqFrame f1 sliceMem) ⟩
       → ⟨ z ∈ˢ F8 a b ⟩
    go (cm , (c∈b , hf)) = subst ⟨_⟩ (sym (F8-spec a b z))
      ∣ fib .fst , (cong (F10 a) (fib .snd) ∙ sym zeq) ∣₁
      where
      c∈C : ⟨ fst cm ∈ˢ C ⟩
      c∈C = snd cm
      fib : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ fst cm)
      fib = ∈-asFiber {a = fst cm} {b = b} c∈b
      zeq : z ≡ F10 a (fst cm)
      zeq = eqFrame-out f1 sliceMem
        (cm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) (F10 a (fst cm))
        (sliceSub a (fst cm) a∈)
        (λ v v∈ k → sliceMem-out z b a y (fst cm) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (λ v v∈ k → sliceMem-in z b a y (fst cm) v z∈ b∈ a∈ y∈ c∈C v∈ k) hf

  mem8-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op8 a b ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem8 ⟩
  mem8-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem8)) go
    (subst ⟨_⟩ (F8-spec a b z) (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f8 a b) h))
    where
    go : Σ[ m ∈ ⟪ b ⟫ ] (F10 a (⟪ b ⟫↪ m) ≡ z)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem8 ⟩
    go (m , e) = ∣ pt (⟪ b ⟫↪ m) c∈C , (c∈b , frame) ∣₁
      where
      c∈b : ⟨ ⟪ b ⟫↪ m ∈ˢ b ⟩
      c∈b = ∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd (∈ₛ⟪ b ⟫↪ m)
      c∈C : ⟨ ⟪ b ⟫↪ m ∈ˢ C ⟩
      c∈C = mem b (⟪ b ⟫↪ m) c∈b b∈
      frame : ⟨ (pt (⟪ b ⟫↪ m) c∈C ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                DefC.⊨ᵐ eqFrame f1 sliceMem ⟩
      frame = eqFrame-in f1 sliceMem
        (pt (⟪ b ⟫↪ m) c∈C ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
        (F10 a (⟪ b ⟫↪ m)) (sliceSub a (⟪ b ⟫↪ m) a∈)
        (λ v v∈ k → sliceMem-out z b a y (⟪ b ⟫↪ m) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (λ v v∈ k → sliceMem-in z b a y (⟪ b ⟫↪ m) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (sym e)
```

<!--en-->
## Recap

A definable subset is carved by a formula read in the inner world, with the
environment spelled out and the membership certificate carried beside each
element; the singleton, the unordered pair and the Kuratowski pair are described
at variables; and one equality frame carries every "this variable is that set"
clause, including the two projections, whose junk the intersection description
places with no case analysis on the left and one reading on the right. Over that
kit sit the sixteen membership formulas at bound arguments, each adequate in both
directions, their disjunction guarded by the two argument clauses, and the step
formula whose definable subset is the step. The offsets are settled separately
and exactly: four stages, discharged by pairing alone plus one image slice and
the empty set. Both facts the bridge's reduction names are now proved, and the
identification of the two towers stands on one hypothesis fewer.
<!--zh-->
## 小结

可定义子集由一条在内层世界读出的公式刻出，其中环境逐项写明、隶属证书与每个元素并肩携带；单点集、无序对与 Kuratowski 对都在变量上描述；而一个等词框架承载每一条「此变量即彼集」的子句，两个投影亦在其中，其垃圾由交的描述安放：左侧无须情形分析，右侧一次读取即可。器材之上是十六条实参受约束的隶属公式，各自双向适足；其析取由两条实参子句看守；而 step 公式的可定义子集正是该步。偏移则另行结清且分毫不差：四个阶段，仅由配对兑现，外加一个像片与空集。桥的归约所点名的两条事实至此皆已证成，两塔的认同又少倚一条假设。
<!--/-->

<!--en-->
## The four tuple operations, over one frame

The four operations that shuffle a pair's components share a frame: bind the two
projections, pin them to the second argument, and let the arm say only how the
value is built from them. The frame is where the projections enter and leave;
the four arms below differ only in the shape of the value, and each is two
readings of the unordered pair.
<!--zh-->
## 四个三元组运算，同用一个框架

搬运对之分量的四个运算共用一个框架：约束两个投影，把它们钉在第二实参上，臂只说该值如何由它们造出。投影在框架处进场与退场；以下四条臂只在值的形状上有别，每条都是无序对的两次读取。
<!--/-->

```agda
  left∈C : (b : S) → ⟨ b ∈ˢ C ⟩ → ⟨ left b ∈ˢ C ⟩
  left∈C b b∈ = go (left-read b b∈)
    where
    go : (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅)) → ⟨ left b ∈ˢ C ⟩
    go (inl h) = h
    go (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) ∅∈C

  right∈C : (b : S) → ⟨ b ∈ˢ C ⟩ → ⟨ right b ∈ˢ C ⟩
  right∈C b b∈ = go (right-read b b∈)
    where
    go : (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅)) → ⟨ right b ∈ˢ C ⟩
    go (inl h) = h
    go (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) ∅∈C

  tupleOut : (shape : Formula ⟪ C ⟫ 6) (z b a y : S)
             (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩) (R : hProp (ℓ-suc ℓ))
           → ((l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
              → l ≡ left b → r ≡ right b
              → ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) DefC.⊨ᵐ shape ⟩
              → ⟨ R ⟩)
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ
               (∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape)))) ⟩
           → ⟨ R ⟩
  tupleOut shape z b a y z∈ b∈ a∈ y∈ R k h = PT.rec (snd R) k0 h
    where
    k0 : Σ[ lm ∈ DefC.SM ]
           ⟨ (lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ
             (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape))) ⟩
       → ⟨ R ⟩
    k0 (lm , h1) = PT.rec (snd R) k1 h1
      where
      k1 : Σ[ rm ∈ DefC.SM ]
             ⟨ ((rm ∷ lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                DefC.⊨ᵐ leftEqF f1 f3)
               ⊓ (((rm ∷ lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                   DefC.⊨ᵐ rightEqF f0 f3)
                 ⊓ ((rm ∷ lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
                    DefC.⊨ᵐ shape)) ⟩
         → ⟨ R ⟩
      k1 (rm , (hl , (hr , hs))) = k (fst lm) (fst rm) (snd lm) (snd rm)
        (leftEqF-out f1 f3
          (rm ∷ lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) hl)
        (rightEqF-out f0 f3
          (rm ∷ lm ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) hr)
        hs

  tupleIn : (shape : Formula ⟪ C ⟫ 6) (z b a y : S)
            (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
               ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ shape ⟩
          → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ
              (∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape)))) ⟩
  tupleIn shape z b a y z∈ b∈ a∈ y∈ hs =
    ∣ pt (left b) (left∈C b b∈)
    , ∣ pt (right b) (right∈C b b∈)
      , (leftEqF-in f1 f3
          (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
           ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) refl
        , (rightEqF-in f0 f3
            (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
             ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) refl
          , hs)) ∣₁ ∣₁

  mem11-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem11 ⟩
            → ⟨ z ∈ˢ Fof op11 a b ⟩
  mem11-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape11 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op11 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          DefC.⊨ᵐ shape11 ⟩
      → ⟨ z ∈ˢ Fof op11 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f11 a b))
      (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) z .snd
        (PT.rec (snd ((z ≡ₕ ⁅ left b ⁆s)
          ⊔ (z ≡ₕ ⁅ left b , pr a (right b) ⁆))) go hs))
      where
      go : ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ sglAt f2 f1 ⟩
         ⊎ ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ (∃̇ (prAt f0 f5 f1 ∧̇ pairAt f3 f2 f0)) ⟩
         → ⟨ (z ≡ₕ ⁅ left b ⁆s) ⊔ (z ≡ₕ ⁅ left b , pr a (right b) ⁆) ⟩
      go (inl s) = ∣ inl (subst (λ w → z ≡ ⁅ w ⁆s) el
        (sglAt-out f2 f1
          (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          s)) ∣₁
      go (inr s) = PT.map inner s
        where
        inner : Σ[ tm ∈ DefC.SM ]
                  ⟨ ((tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                      ∷ pt y y∈ ∷ []) DefC.⊨ᵐ prAt f0 f5 f1)
                    ⊓ ((tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                        ∷ pt y y∈ ∷ []) DefC.⊨ᵐ pairAt f3 f2 f0) ⟩
              → (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr a (right b) ⁆)
        inner (tm , (e1 , e2)) = inr
          (subst (λ w → z ≡ ⁅ w , pr a (right b) ⁆) el
            (subst (λ w → z ≡ ⁅ l , pr a w ⁆) er
              (subst (λ w → z ≡ ⁅ l , w ⁆)
                (prAt-out f0 f5 f1
                  (tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e1)
                (pairAt-out f3 f2 f0
                  (tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e2))))

  mem11-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op11 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem11 ⟩
  mem11-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem11)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f11 a b) h))
    where
    go : (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr a (right b) ⁆)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem11 ⟩
    go (inl e) = tupleIn shape11 z b a y z∈ b∈ a∈ y∈
      ∣ inl (sglAt-in f2 f1
        (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
         ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) ∣₁
    go (inr e) = tupleIn shape11 z b a y z∈ b∈ a∈ y∈
      ∣ inr ∣ pt (pr a (right b)) t∈C
        , (prAt-in f0 f5 f1
            (pt (pr a (right b)) t∈C ∷ pt (right b) (right∈C b b∈)
             ∷ pt (left b) (left∈C b b∈) ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
             ∷ pt y y∈ ∷ []) refl
          , pairAt-in f3 f2 f0
              (pt (pr a (right b)) t∈C ∷ pt (right b) (right∈C b b∈)
               ∷ pt (left b) (left∈C b b∈) ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
               ∷ pt y y∈ ∷ []) e) ∣₁ ∣₁
      where
      t∈C : ⟨ pr a (right b) ∈ˢ C ⟩
      t∈C = mem z (pr a (right b))
        (subst (λ w → ⟨ pr a (right b) ∈ˢ w ⟩) (sym e)
          (F0-spec (left b) (pr a (right b)) (pr a (right b)) .snd
            ∣ inr refl ∣₁)) z∈

  mem12-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem12 ⟩
            → ⟨ z ∈ˢ Fof op12 a b ⟩
  mem12-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape12 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op12 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          DefC.⊨ᵐ shape12 ⟩
      → ⟨ z ∈ˢ Fof op12 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f12 a b))
      (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) z .snd
        (PT.rec (snd ((z ≡ₕ ⁅ left b ⁆s)
          ⊔ (z ≡ₕ ⁅ left b , pr (right b) a ⁆))) go hs))
      where
      go : ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ sglAt f2 f1 ⟩
         ⊎ ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ (∃̇ (prAt f0 f1 f5 ∧̇ pairAt f3 f2 f0)) ⟩
         → ⟨ (z ≡ₕ ⁅ left b ⁆s) ⊔ (z ≡ₕ ⁅ left b , pr (right b) a ⁆) ⟩
      go (inl s) = ∣ inl (subst (λ w → z ≡ ⁅ w ⁆s) el
        (sglAt-out f2 f1
          (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          s)) ∣₁
      go (inr s) = PT.map inner s
        where
        inner : Σ[ tm ∈ DefC.SM ]
                  ⟨ ((tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                      ∷ pt y y∈ ∷ []) DefC.⊨ᵐ prAt f0 f1 f5)
                    ⊓ ((tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                        ∷ pt y y∈ ∷ []) DefC.⊨ᵐ pairAt f3 f2 f0) ⟩
              → (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr (right b) a ⁆)
        inner (tm , (e1 , e2)) = inr
          (subst (λ w → z ≡ ⁅ w , pr (right b) a ⁆) el
            (subst (λ w → z ≡ ⁅ l , pr w a ⁆) er
              (subst (λ w → z ≡ ⁅ l , w ⁆)
                (prAt-out f0 f1 f5
                  (tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e1)
                (pairAt-out f3 f2 f0
                  (tm ∷ pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
                   ∷ pt y y∈ ∷ []) e2))))

  mem12-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op12 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem12 ⟩
  mem12-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem12)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f12 a b) h))
    where
    go : (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr (right b) a ⁆)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem12 ⟩
    go (inl e) = tupleIn shape12 z b a y z∈ b∈ a∈ y∈
      ∣ inl (sglAt-in f2 f1
        (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
         ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) ∣₁
    go (inr e) = tupleIn shape12 z b a y z∈ b∈ a∈ y∈
      ∣ inr ∣ pt (pr (right b) a) t∈C
        , (prAt-in f0 f1 f5
            (pt (pr (right b) a) t∈C ∷ pt (right b) (right∈C b b∈)
             ∷ pt (left b) (left∈C b b∈) ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
             ∷ pt y y∈ ∷ []) refl
          , pairAt-in f3 f2 f0
              (pt (pr (right b) a) t∈C ∷ pt (right b) (right∈C b b∈)
               ∷ pt (left b) (left∈C b b∈) ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈
               ∷ pt y y∈ ∷ []) e) ∣₁ ∣₁
      where
      t∈C : ⟨ pr (right b) a ∈ˢ C ⟩
      t∈C = mem z (pr (right b) a)
        (subst (λ w → ⟨ pr (right b) a ∈ˢ w ⟩) (sym e)
          (F0-spec (left b) (pr (right b) a) (pr (right b) a) .snd
            ∣ inr refl ∣₁)) z∈

  mem13-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem13 ⟩
            → ⟨ z ∈ˢ Fof op13 a b ⟩
  mem13-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape13 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op13 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          DefC.⊨ᵐ shape13 ⟩
      → ⟨ z ∈ˢ Fof op13 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f13 a b))
      (F0-spec (left b) (pr (right b) a) z .snd (PT.map go hs))
      where
      go : (z ≡ l)
         ⊎ ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ prAt f2 f0 f4 ⟩
         → (z ≡ left b) ⊎ (z ≡ pr (right b) a)
      go (inl e) = inl (subst (λ w → z ≡ w) el e)
      go (inr s) = inr (subst (λ w → z ≡ pr w a) er
        (prAt-out f2 f0 f4
          (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          s))

  mem13-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op13 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem13 ⟩
  mem13-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem13)) go
    (F0-spec (left b) (pr (right b) a) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f13 a b) h))
    where
    go : (z ≡ left b) ⊎ (z ≡ pr (right b) a)
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem13 ⟩
    go (inl e) = tupleIn shape13 z b a y z∈ b∈ a∈ y∈ ∣ inl e ∣₁
    go (inr e) = tupleIn shape13 z b a y z∈ b∈ a∈ y∈
      ∣ inr (prAt-in f2 f0 f4
        (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
         ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) ∣₁

  mem14-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem14 ⟩
            → ⟨ z ∈ˢ Fof op14 a b ⟩
  mem14-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape14 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op14 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          DefC.⊨ᵐ shape14 ⟩
      → ⟨ z ∈ˢ Fof op14 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f14 a b))
      (F0-spec (left b) (pr a (right b)) z .snd (PT.map go hs))
      where
      go : (z ≡ l)
         ⊎ ⟨ (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
             DefC.⊨ᵐ prAt f2 f4 f0 ⟩
         → (z ≡ left b) ⊎ (z ≡ pr a (right b))
      go (inl e) = inl (subst (λ w → z ≡ w) el e)
      go (inr s) = inr (subst (λ w → z ≡ pr a w) er
        (prAt-out f2 f4 f0
          (pt r r∈ ∷ pt l l∈ ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ [])
          s))

  mem14-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op14 a b ⟩
           → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem14 ⟩
  mem14-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem14)) go
    (F0-spec (left b) (pr a (right b)) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f14 a b) h))
    where
    go : (z ≡ left b) ⊎ (z ≡ pr a (right b))
       → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ mem14 ⟩
    go (inl e) = tupleIn shape14 z b a y z∈ b∈ a∈ y∈ ∣ inl e ∣₁
    go (inr e) = tupleIn shape14 z b a y z∈ b∈ a∈ y∈
      ∣ inr (prAt-in f2 f4 f0
        (pt (right b) (right∈C b b∈) ∷ pt (left b) (left∈C b b∈)
         ∷ pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) e) ∣₁
```

<!--en-->
## The sixteen graphs, and the step

The arms assemble in two moves. First, each membership formula becomes a
**graph** by the equality frame: the value of the operation at the two bound
arguments is exactly the set the fourth variable names, provided the value is a
subset of the carrier, which the consumer always has. Second, the sixteen graphs
are disjoined, and the disjunction is guarded by the two argument clauses, so
the whole formula reads: "a member of the set, or the set itself, or the value of
one of the sixteen operations at two arguments drawn from the set and itself".
That is the rud step, verbatim, and the definable subset it carves is the step.
<!--zh-->
## 十六个图，与 step

诸臂分两步装配。其一，每条隶属公式经等词框架成为一个**图**：该运算在两个受约束实参处的值恰是第四个变量所指的集合，前提是该值为载体的子集，而消费者总是持有这一条。其二，十六个图作析取，析取又由两条实参子句看守，于是整条公式读作：「该集合的一个成员，或该集合自身，或十六个运算之一在取自该集合及其自身的两个实参处的值」。这逐字就是一步初步函数，而它刻出的可定义子集正是该步。
<!--/-->

```agda
  memOf : Op16 → Formula ⟪ C ⟫ 4
  memOf op0 = mem0
  memOf op1 = mem1
  memOf op2 = mem2
  memOf op3 = mem3
  memOf op4 = mem4
  memOf op5 = mem5
  memOf op6 = mem6
  memOf op7 = mem7
  memOf op8 = mem8
  memOf op9 = mem9
  memOf op10 = mem10
  memOf op11 = mem11
  memOf op12 = mem12
  memOf op13 = mem13
  memOf op14 = mem14
  memOf op15 = mem15

  memOut : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
           (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
         → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ memOf i ⟩
         → ⟨ z ∈ˢ Fof i a b ⟩
  memOut op0 = mem0-out
  memOut op1 = mem1-out
  memOut op2 = mem2-out
  memOut op3 = mem3-out
  memOut op4 = mem4-out
  memOut op5 = mem5-out
  memOut op6 = mem6-out
  memOut op7 = mem7-out
  memOut op8 = mem8-out
  memOut op9 = mem9-out
  memOut op10 = mem10-out
  memOut op11 = mem11-out
  memOut op12 = mem12-out
  memOut op13 = mem13-out
  memOut op14 = mem14-out
  memOut op15 = mem15-out

  memIn : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
          (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
        → ⟨ z ∈ˢ Fof i a b ⟩
        → ⟨ (pt z z∈ ∷ pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ memOf i ⟩
  memIn op0 = mem0-in
  memIn op1 = mem1-in
  memIn op2 = mem2-in
  memIn op3 = mem3-in
  memIn op4 = mem4-in
  memIn op5 = mem5-in
  memIn op6 = mem6-in
  memIn op7 = mem7-in
  memIn op8 = mem8-in
  memIn op9 = mem9-in
  memIn op10 = mem10-in
  memIn op11 = mem11-in
  memIn op12 = mem12-in
  memIn op13 = mem13-in
  memIn op14 = mem14-in
  memIn op15 = mem15-in

  graphOf : Op16 → Formula ⟪ C ⟫ 3
  graphOf i = eqFrame f2 (memOf i)

  graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
            → ⟨ (pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ graphOf i ⟩
            → y ≡ Fof i a b
  graph-out i b a y b∈ a∈ y∈ sub h = eqFrame-out f2 (memOf i)
    (pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) (Fof i a b) sub
    (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
    (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) h

  graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
           → y ≡ Fof i a b
           → ⟨ (pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) DefC.⊨ᵐ graphOf i ⟩
  graph-in i b a y b∈ a∈ y∈ sub e = eqFrame-in f2 (memOf i)
    (pt b b∈ ∷ pt a a∈ ∷ pt y y∈ ∷ []) (Fof i a b) sub
    (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
    (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) e

  orTail0 orTail1 orTail2 orTail3 orTail4 orTail5 orTail6 orTail7 : Formula ⟪ C ⟫ 3
  orTail8 orTail9 orTail10 orTail11 orTail12 orTail13 orTail14 orTail15 :
    Formula ⟪ C ⟫ 3
  orTail0 = graphOf op0 ∨̇ orTail1
  orTail1 = graphOf op1 ∨̇ orTail2
  orTail2 = graphOf op2 ∨̇ orTail3
  orTail3 = graphOf op3 ∨̇ orTail4
  orTail4 = graphOf op4 ∨̇ orTail5
  orTail5 = graphOf op5 ∨̇ orTail6
  orTail6 = graphOf op6 ∨̇ orTail7
  orTail7 = graphOf op7 ∨̇ orTail8
  orTail8 = graphOf op8 ∨̇ orTail9
  orTail9 = graphOf op9 ∨̇ orTail10
  orTail10 = graphOf op10 ∨̇ orTail11
  orTail11 = graphOf op11 ∨̇ orTail12
  orTail12 = graphOf op12 ∨̇ orTail13
  orTail13 = graphOf op13 ∨̇ orTail14
  orTail14 = graphOf op14 ∨̇ orTail15
  orTail15 = graphOf op15

  bigOr : Formula ⟪ C ⟫ 3
  bigOr = orTail0

  bigOr-in : (i : Op16) (δ : Vec DefC.SM 3)
           → ⟨ δ DefC.⊨ᵐ graphOf i ⟩ → ⟨ δ DefC.⊨ᵐ bigOr ⟩
  bigOr-in op0 δ h = ∣ inl h ∣₁
  bigOr-in op1 δ h = ∣ inr ∣ inl h ∣₁ ∣₁
  bigOr-in op2 δ h = ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁
  bigOr-in op3 δ h = ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op4 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op5 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op6 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op7 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op8 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op9 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op10 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op11 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op12 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op13 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op14 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
  bigOr-in op15 δ h =
    ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr
      ∣ inr ∣ inr ∣ inr h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

  orStep : (φ ψ : Formula ⟪ C ⟫ 3) (δ : Vec DefC.SM 3)
           (R : hProp (ℓ-suc ℓ))
         → (⟨ δ DefC.⊨ᵐ φ ⟩ → ⟨ R ⟩) → (⟨ δ DefC.⊨ᵐ ψ ⟩ → ⟨ R ⟩)
         → ⟨ δ DefC.⊨ᵐ (φ ∨̇ ψ) ⟩ → ⟨ R ⟩
  orStep φ ψ δ R f g = PT.rec (snd R) (Sum.rec f g)

  bigOr-out : (δ : Vec DefC.SM 3) (R : hProp (ℓ-suc ℓ))
            → ((i : Op16) → ⟨ δ DefC.⊨ᵐ graphOf i ⟩ → ⟨ R ⟩)
            → ⟨ δ DefC.⊨ᵐ bigOr ⟩ → ⟨ R ⟩
  bigOr-out δ R k = go0
    where
    go15 : ⟨ δ DefC.⊨ᵐ orTail15 ⟩ → ⟨ R ⟩
    go15 = k op15
    go14 : ⟨ δ DefC.⊨ᵐ orTail14 ⟩ → ⟨ R ⟩
    go14 = orStep (graphOf op14) orTail15 δ R (k op14) go15
    go13 : ⟨ δ DefC.⊨ᵐ orTail13 ⟩ → ⟨ R ⟩
    go13 = orStep (graphOf op13) orTail14 δ R (k op13) go14
    go12 : ⟨ δ DefC.⊨ᵐ orTail12 ⟩ → ⟨ R ⟩
    go12 = orStep (graphOf op12) orTail13 δ R (k op12) go13
    go11 : ⟨ δ DefC.⊨ᵐ orTail11 ⟩ → ⟨ R ⟩
    go11 = orStep (graphOf op11) orTail12 δ R (k op11) go12
    go10 : ⟨ δ DefC.⊨ᵐ orTail10 ⟩ → ⟨ R ⟩
    go10 = orStep (graphOf op10) orTail11 δ R (k op10) go11
    go9 : ⟨ δ DefC.⊨ᵐ orTail9 ⟩ → ⟨ R ⟩
    go9 = orStep (graphOf op9) orTail10 δ R (k op9) go10
    go8 : ⟨ δ DefC.⊨ᵐ orTail8 ⟩ → ⟨ R ⟩
    go8 = orStep (graphOf op8) orTail9 δ R (k op8) go9
    go7 : ⟨ δ DefC.⊨ᵐ orTail7 ⟩ → ⟨ R ⟩
    go7 = orStep (graphOf op7) orTail8 δ R (k op7) go8
    go6 : ⟨ δ DefC.⊨ᵐ orTail6 ⟩ → ⟨ R ⟩
    go6 = orStep (graphOf op6) orTail7 δ R (k op6) go7
    go5 : ⟨ δ DefC.⊨ᵐ orTail5 ⟩ → ⟨ R ⟩
    go5 = orStep (graphOf op5) orTail6 δ R (k op5) go6
    go4 : ⟨ δ DefC.⊨ᵐ orTail4 ⟩ → ⟨ R ⟩
    go4 = orStep (graphOf op4) orTail5 δ R (k op4) go5
    go3 : ⟨ δ DefC.⊨ᵐ orTail3 ⟩ → ⟨ R ⟩
    go3 = orStep (graphOf op3) orTail4 δ R (k op3) go4
    go2 : ⟨ δ DefC.⊨ᵐ orTail2 ⟩ → ⟨ R ⟩
    go2 = orStep (graphOf op2) orTail3 δ R (k op2) go3
    go1 : ⟨ δ DefC.⊨ᵐ orTail1 ⟩ → ⟨ R ⟩
    go1 = orStep (graphOf op1) orTail2 δ R (k op1) go2
    go0 : ⟨ δ DefC.⊨ᵐ orTail0 ⟩ → ⟨ R ⟩
    go0 = orStep (graphOf op0) orTail1 δ R (k op0) go1
```

<!--en-->
## The step formula, and the theorem

The formula is assembled at the argument of the step: the two floor clauses take
the set as a constant, and the image clause binds the two arguments, tests each
against the set and itself, and hands them to the sixteen graphs. Both directions
of the description are the step's own membership characterization read off arm by
arm; nothing else enters. The theorem then places the step in the next stage,
because a definable subset of a stage is a member of the stage above it.
<!--zh-->
## step 公式，与定理

公式在 step 的实参处装配：两条地板子句把该集合取作常量，像子句约束两个实参、分别对该集合及其自身作检验，再交给十六个图。描述的两个方向都是 step 自身的隶属刻画逐臂读出，别无其他。定理随之把该步安放进下一阶段，因为一个阶段的可定义子集是其上一阶段的成员。
<!--/-->

```agda
  module AtStep (u : S) (mu : ⟪ C ⟫) (qu : ⟪ C ⟫↪ mu ≡ u)
                (stepSub : (v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ C ⟩) where

    u∈C : ⟨ u ∈ˢ C ⟩
    u∈C = stepSub u (step-in-self u)

    argIn : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ C ⟩
    argIn c (inl h) = mem u c h u∈C
    argIn c (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) u∈C

    argIn' : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ u' u ⟩
    argIn' c (inl h) = u'-in u c h
    argIn' c (inr e) = subst (λ w → ⟨ w ∈ˢ u' u ⟩) (sym e) (u-self-in u)

    inU : {n : ℕ} → Fin n → Formula ⟪ C ⟫ n
    inU k = (var k ∈̇ con mu) ∨̇ (var k ≐ con mu)

    inU-out : {n : ℕ} (k : Fin n) (δ : Vec DefC.SM n)
            → ⟨ δ DefC.⊨ᵐ inU k ⟩
            → ∥ (⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u)) ∥₁
    inU-out k δ h = PT.map go h
      where
      go : ⟨ fst (lookup k δ) ∈ˢ ⟪ C ⟫↪ mu ⟩ ⊎ (fst (lookup k δ) ≡ ⟪ C ⟫↪ mu)
         → ⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u)
      go (inl m) = inl (subst (λ w → ⟨ fst (lookup k δ) ∈ˢ w ⟩) qu m)
      go (inr e) = inr (e ∙ qu)

    inU-in : {n : ℕ} (k : Fin n) (δ : Vec DefC.SM n)
           → (⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u))
           → ⟨ δ DefC.⊨ᵐ inU k ⟩
    inU-in k δ (inl m) =
      ∣ inl (subst (λ w → ⟨ fst (lookup k δ) ∈ˢ w ⟩) (sym qu) m) ∣₁
    inU-in k δ (inr e) = ∣ inr (e ∙ sym qu) ∣₁

    imgForm : Formula ⟪ C ⟫ 1
    imgForm = ∃̇ (∃̇ (inU f1 ∧̇ (inU f0 ∧̇ bigOr)))

    stepForm : Formula ⟪ C ⟫ 1
    stepForm = inU f0 ∨̇ imgForm

    valueSub : (i : Op16) (a b v : S) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
             → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) → (w : S) → ⟨ w ∈ˢ Fof i a b ⟩
             → ⟨ w ∈ˢ C ⟩
    valueSub i a b v sa sb w hw = mem (Fof i a b) w hw
      (stepSub (Fof i a b)
        (step-in-img u (Fof i a b) i a b (argIn' a sa) (argIn' b sb) refl))

    din : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ step u ⟩
        → ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ stepForm ⟩
    din v v∈ h = PT.rec (snd ((pt v v∈ ∷ []) DefC.⊨ᵐ stepForm)) go
      (step-out u v h)
      where
      go : StepArm u v → ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ stepForm ⟩
      go (arm-member m) = ∣ inl (inU-in f0 (pt v v∈ ∷ []) (inl m)) ∣₁
      go (arm-self e) = ∣ inl (inU-in f0 (pt v v∈ ∷ []) (inr e)) ∣₁
      go (arm-image i a b sa sb e) =
        ∣ inr ∣ pt a (argIn a sa) , ∣ pt b (argIn b sb)
          , (inU-in f1 (pt b (argIn b sb) ∷ pt a (argIn a sa) ∷ pt v v∈ ∷ []) sa
            , (inU-in f0
                (pt b (argIn b sb) ∷ pt a (argIn a sa) ∷ pt v v∈ ∷ []) sb
              , bigOr-in i
                  (pt b (argIn b sb) ∷ pt a (argIn a sa) ∷ pt v v∈ ∷ [])
                  (graph-in i b a v (argIn b sb) (argIn a sa) v∈
                    (valueSub i a b v sa sb) e))) ∣₁ ∣₁ ∣₁

    dout : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
         → ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ stepForm ⟩ → ⟨ v ∈ˢ step u ⟩
    dout v v∈ h = PT.rec (snd (v ∈ˢ step u)) branch h
      where
      floor : ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ inU f0 ⟩ → ⟨ v ∈ˢ step u ⟩
      floor hf = PT.rec (snd (v ∈ˢ step u)) go
        (inU-out f0 (pt v v∈ ∷ []) hf)
        where
        go : (⟨ v ∈ˢ u ⟩ ⊎ (v ≡ u)) → ⟨ v ∈ˢ step u ⟩
        go (inl m) = step-in u v m
        go (inr e) =
          subst (λ w → ⟨ w ∈ˢ step u ⟩) (sym e) (step-in-self u)
      img : ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ imgForm ⟩ → ⟨ v ∈ˢ step u ⟩
      img hi = PT.rec (snd (v ∈ˢ step u)) k0 hi
        where
        k0 : Σ[ am ∈ DefC.SM ]
               ⟨ (am ∷ pt v v∈ ∷ []) DefC.⊨ᵐ
                 (∃̇ (inU f1 ∧̇ (inU f0 ∧̇ bigOr))) ⟩
           → ⟨ v ∈ˢ step u ⟩
        k0 (am , h1) = PT.rec (snd (v ∈ˢ step u)) k1 h1
          where
          k1 : Σ[ bm ∈ DefC.SM ]
                 ⟨ ((bm ∷ am ∷ pt v v∈ ∷ []) DefC.⊨ᵐ inU f1)
                   ⊓ (((bm ∷ am ∷ pt v v∈ ∷ []) DefC.⊨ᵐ inU f0)
                     ⊓ ((bm ∷ am ∷ pt v v∈ ∷ []) DefC.⊨ᵐ bigOr)) ⟩
             → ⟨ v ∈ˢ step u ⟩
          k1 (bm , (ha , (hb , hor))) =
            PT.rec (snd (v ∈ˢ step u)) k2
              (inU-out f1 (bm ∷ am ∷ pt v v∈ ∷ []) ha)
            where
            k2 : (⟨ fst am ∈ˢ u ⟩ ⊎ (fst am ≡ u)) → ⟨ v ∈ˢ step u ⟩
            k2 sa = PT.rec (snd (v ∈ˢ step u)) k3
              (inU-out f0 (bm ∷ am ∷ pt v v∈ ∷ []) hb)
              where
              k3 : (⟨ fst bm ∈ˢ u ⟩ ⊎ (fst bm ≡ u)) → ⟨ v ∈ˢ step u ⟩
              k3 sb = bigOr-out (bm ∷ am ∷ pt v v∈ ∷ []) (v ∈ˢ step u) k4 hor
                where
                k4 : (i : Op16)
                   → ⟨ (bm ∷ am ∷ pt v v∈ ∷ []) DefC.⊨ᵐ graphOf i ⟩
                   → ⟨ v ∈ˢ step u ⟩
                k4 i hg = step-in-img u v i (fst am) (fst bm)
                  (argIn' (fst am) sa) (argIn' (fst bm) sb)
                  (graph-out i (fst bm) (fst am) v (snd bm) (snd am) v∈
                    (valueSub i (fst am) (fst bm) v sa sb) hg)
      branch : ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ inU f0 ⟩
             ⊎ ⟨ (pt v v∈ ∷ []) DefC.⊨ᵐ imgForm ⟩
             → ⟨ v ∈ˢ step u ⟩
      branch (inl hf) = floor hf
      branch (inr hi) = img hi

    stepSet-desc : DefC.defSet stepForm ≡ step u
    stepSet-desc = described stepForm (step u) stepSub din dout
```

<!--en-->
The empty set is a definable subset of every stage below a stage that already
holds something, which is what places the relativization slot of the plain trunk
and, with it, the last hypothesis the description needs.
<!--zh-->
空集是任何阶段的可定义子集，只要该阶段之下已有一个阶段收下了什么，这既安放了非相对化主干的相对化槽，也随之安放了描述所需的最后一条假设。
<!--/-->

```agda
∅∈Lset : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ⟨ ∅ ∈ˢ Lset ζ ⟩
∅∈Lset u ζ u∈ = PT.rec (snd (∅ ∈ˢ Lset ζ)) go (Lset-out ζ u u∈)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ζ ⟩ × ⟨ u ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ ∅ ∈ˢ Lset ζ ⟩
  go (δ , δ∈ζ , _) = Lset-in ζ δ ∅ δ∈ζ
    (subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset δ) ⟩) (defSet⊥≡∅ (Lset δ))
      (𝒟ₒ-intro (Lset δ) (DefOf.defSet (Lset δ) ⊥̇) ∣ ⊥̇ , refl ∣₁))

stepSet∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ⟨ A ∈ˢ Lset ζ ⟩
          → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
          → ⟨ step u ∈ˢ Lset (sucV ζ) ⟩
stepSet∈L u ζ u∈ A∈ sub = 𝒟ₒ⊆Lsuc ζ (step u)
  (𝒟ₒ-intro (Lset ζ) (step u) ∣ St.stepForm , St.stepSet-desc ∣₁)
  where
  fibA : Σ[ m ∈ ⟪ Lset ζ ⟫ ] (⟪ Lset ζ ⟫↪ m ≡ A)
  fibA = ∈-asFiber {a = A} {b = Lset ζ} A∈
  fibu : Σ[ m ∈ ⟪ Lset ζ ⟫ ] (⟪ Lset ζ ⟫↪ m ≡ u)
  fibu = ∈-asFiber {a = u} {b = Lset ζ} u∈
  module Sl = Slot (Lset ζ) (Ltr ζ) (fibA .fst) (fibA .snd) (∅∈Lset u ζ u∈)
  module St = Sl.AtStep u (fibu .fst) (fibu .snd) sub
```
