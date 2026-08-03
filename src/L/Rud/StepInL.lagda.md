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
open import L.Constructible {ℓ} using ( Lset; Lset-mono; 𝒟ₒ-intro )
open import L.Rud.Ops {ℓ} using
  ( F0; F0-spec; F1-spec; F2-read; F2-write; F3-read; F3-write; F4-read
  ; F4-write; F5-spec; F6-read; F6-write; F7-read; F7-write )
open import L.Rud.Images {ℓ} using
  ( F8; F8-spec; F10; F10-spec; left; left-spec; right; right-spec
  ; right-nonpair; ⋂; ⋂-member-in-all; left-⋂-collapse; left-⋂-empty
  ; module F15Of )
open import L.Rud.Describe {ℓ} using ( module F10Desc )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; Fof; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5
  ; Fof-f6; Fof-f7; Fof-f8; Fof-f9; Fof-f10; Fof-f11; Fof-f12; Fof-f13
  ; Fof-f14; Fof-f15; singl≡pair; isPair )
open import L.Rud.Bridge {ℓ} lem A using
  ( 𝒟ₒ⊆Lsuc; Ltr; Lpair; ValuesInU; suc⁴; empty-⊆; ext-⊆ )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
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
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym right≡q)
        (prR∈ p q (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
        where
        right≡q : right b ≡ q
        right≡q = subst (λ w → right w ≡ q) (sym b≡) (right-spec p q)
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
    all z z∈ = PT.map step (h₃ (pt z (entry∈ q δ z z∈)) z∈)
      where
      step : ⟨ (pt z (entry∈ q δ z z∈) ∷ δ) DefC.⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (pt z (entry∈ q δ z z∈) ∷ δ) DefC.⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
           → (z ≡ ⁅ U ⁆s) ⊎ (z ≡ ⁅ U , W ⁆)
      step (inl s) = inl (sglAt-out f0 (suc u) (pt z (entry∈ q δ z z∈) ∷ δ) s)
      step (inr s) =
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
    part₃ xm h = PT.map step
      (F0-spec (⁅ U ⁆s) (⁅ U , W ⁆) (fst xm) .fst
        (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h))
      where
      step : (fst xm ≡ ⁅ U ⁆s) ⊎ (fst xm ≡ ⁅ U , W ⁆)
           → ⟨ (xm ∷ δ) DefC.⊨ᵐ sglAt f0 (suc u) ⟩
           ⊎ ⟨ (xm ∷ δ) DefC.⊨ᵐ pairAt f0 (suc u) (suc v) ⟩
      step (inl s) = inl (sglAt-in f0 (suc u) (xm ∷ δ) s)
      step (inr s) = inr (pairAt-in f0 (suc u) (suc v) (xm ∷ δ) s)
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

  leftEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  leftEqF lk bk =
    (∃̇ (∃̇ (prAt (suc (suc bk)) f1 f0 ∧̇ (var (suc (suc lk)) ≐ var f1))))
    ∨̇ ((¬̇ isPairF bk)
      ∧̇ ((∃̇ (capF (suc bk) f0 ∧̇ (var (suc lk) ≐ var f0)))
        ∨̇ ((¬̇ (∃̇ (capF (suc bk) f0))) ∧̇ (∀̇∈ (var lk) ⊥̇))))

  rightEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  rightEqF rk bk =
    (∃̇ (∃̇ (prAt (suc (suc bk)) f1 f0 ∧̇ (var (suc (suc rk)) ≐ var f0))))
    ∨̇ ((¬̇ isPairF bk) ∧̇ (∀̇∈ (var rk) ⊥̇))

module Slot (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C))
            (mA : ⟪ C ⟫) (qA : ⟪ C ⟫↪ mA ≡ A) where

  open Reads C Ctr
  open Desc C Ctr

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
  mem11 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3
            ∧̇ (sglAt f2 f1 ∨̇ (∃̇ (prAt f0 f5 f1 ∧̇ pairAt f3 f2 f0))))))
  mem12 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3
            ∧̇ (sglAt f2 f1 ∨̇ (∃̇ (prAt f0 f1 f5 ∧̇ pairAt f3 f2 f0))))))
  mem13 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3
            ∧̇ ((var f2 ≐ var f1) ∨̇ prAt f2 f0 f4))))
  mem14 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3
            ∧̇ ((var f2 ≐ var f1) ∨̇ prAt f2 f4 f0))))
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

The reading kit is in place: a definable subset is carved by a formula read in
the inner world, with the environment spelled out and the membership certificate
carried beside each element; the singleton, the unordered pair and the Kuratowski
pair are described at variables; and one equality frame carries every "this
variable is that set" clause. Over that kit sit the sixteen membership formulas
at bound arguments, twelve of them with their adequacy in both directions. The
offsets are settled separately and exactly: four stages, discharged by pairing
alone plus one image slice and the empty set.
<!--zh-->
## 小结

读法器材已就位：可定义子集由一条在内层世界读出的公式刻出，其中环境逐项写明、隶属证书与每个元素并肩携带；单点集、无序对与 Kuratowski 对都在变量上描述；而一个等词框架承载每一条「此变量即彼集」的子句。器材之上是十六条实参受约束的隶属公式，其中十二条附有双向适足性。偏移则另行结清且分毫不差：四个阶段，仅由配对兑现，外加一个像片与空集。
<!--/-->
