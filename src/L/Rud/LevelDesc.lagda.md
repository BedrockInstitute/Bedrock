# Descriptions at a level

<!--en-->
The switch theorem left its description side conditioned on one hypothesis: the
image arm, which asks for a defining formula for every one-step image value that
happens to be a subset of the carrier. The description chapter delivers the
sixteen formulas at arguments that are **members** of the carrier; the switch's
own arm allows an argument to be the carrier itself, and that case the
descriptions as delivered do not cover.

This chapter discharges the arm at a **level of the tower**, where the carrier is
`J α` for a limit `α`. A level carries three facts the abstract transitive
carrier does not: it is closed under the sixteen operations, it is its own union,
and it is not a member of itself. Those three turn the plain-argument case into a
single line (the value is a member of the level, so the member arm applies), and
they collapse most of the level-parameter cases as well. What is left is
described by **bounded descent**: when the level stands in an argument slot the
membership test against it is discharged by transitivity, and the quantifier it
used to bind is re-bound inside the candidate itself, which keeps every formula
Δ₀. All sixteen operations close, so the switch's image arm is discharged and its
limit corollary loses that hypothesis.
<!--zh-->
领悟定理的描述一侧留下一条假设：像臂，它要求为每个恰好是载体子集的单步像值给出一条定义公式。描述章交付的十六条公式，其实参都是载体的**成员**；而领悟自家的臂允许某个实参就是载体本身，那一情形现交付的诸描述并不覆盖。

本章在**塔的一层**处清偿该臂，此处载体是极限 `α` 处的 `J α`。层携带三条抽象传递载体所无的事实：它对十六个运算封闭、它是自身之并、且它不属于自身。这三条把平实参情形压成一行 (值是层的成员，故成员臂适用)，也让层参数情形大半坍缩。剩下的用**有界下降**描述：当层站在某个实参槽上，对它的隶属检验由传递性兑清，而它原本约束的量词改在候选自身内部重新约束，于是每条公式都保持 Δ₀。十六个运算全部闭合，故领悟的像臂已清偿，其极限推论也甩掉那条假设。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.LevelDesc {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ⊤̇; ⊥̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Rud.Ops {ℓ} using
  ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write
  ; F3; F3-read; F3-write; F4; F4-read; F4-write; F5; F5-spec
  ; F6; F6-read; F6-write; F7; F7-read; F7-write; F9-spec )
open import L.Rud.Images {ℓ} using
  ( F8; F8-spec; F10; F10-spec; left; right; module F15Of )
open import L.Coding.Base {ℓ} using ( prChar-fwd; prChar-bwd )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; Fof; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5
  ; Fof-f6; Fof-f7; Fof-f8; Fof-f9; Fof-f10; Fof-f11; Fof-f12; Fof-f13
  ; Fof-f14; Fof-f15; F15A
  ; step; Sset; Sset-out; Sset-suc; Sset-mem; Sset-mono; Jset; Jset-rud
  ; prL-in-doubleUnion
  ; Sset-trans
  ; limit-succ-mem )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Switch {ℓ} lem A using ( module Descr )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
open Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _⊆_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality )
-- lint-agda: keep (used qualified: SetPackage.classification)
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; SingletonPackage; SetPackage; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The pair reader, once more

The descent formulas below say "the candidate is the Kuratowski pair of these two
bound variables", so they need the pair reader. The coding chapter wrote it over
its own constant domain and the description chapter restated it over an arbitrary
one; the reader mentions no constants, so it is restated here a third time, clause
for clause, because both earlier copies are private to their chapters. Fixed de
Bruijn indices are named once.
<!--zh-->
## 对读式，再来一次

下面的下降公式要说「候选是这两个约束变量的 Kuratowski 对」，故需要对读式。编码章在自己的常量域上写过它，描述章又在任意域上重述过；读式不提任何常量，故此处第三次逐子句重述，因为前两份都是各自章内的私有物。固定的 de Bruijn 序号一次命名。
<!--/-->

```agda
private
  d0 : {n : ℕ} → Fin (suc n)
  d0 = zero
  d1 : {n : ℕ} → Fin (suc (suc n))
  d1 = suc d0
  d2 : {n : ℕ} → Fin (suc (suc (suc n)))
  d2 = suc d1
  d3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  d3 = suc d2
  d4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
  d4 = suc d3
  d5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
  d5 = suc d4
  d6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  d6 = suc d5
  d7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  d7 = suc d6

  sglAt′ : {K : Type ℓ} {n : ℕ} → Fin n → Fin n → Formula K n
  sglAt′ k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

  pairAt′ : {K : Type ℓ} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  pairAt′ k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
              ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

  prAt′ : {K : Type ℓ} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  prAt′ q u v = (∃̇∈ (var q) (sglAt′ zero (suc u)))
             ∧̇ ((∃̇∈ (var q) (pairAt′ zero (suc u) (suc v)))
             ∧̇ (∀̇∈ (var q) (sglAt′ zero (suc u) ∨̇ pairAt′ zero (suc u) (suc v))))

  Δ₀-sglAt′ : {K : Type ℓ} {n : ℕ} (k i : Fin n) → Δ₀ (sglAt′ {K = K} k i)
  Δ₀-sglAt′ k i = δ-∧ δ-∈ (δ-∀∈ δ-≐)

  Δ₀-pairAt′ : {K : Type ℓ} {n : ℕ} (k i j : Fin n) → Δ₀ (pairAt′ {K = K} k i j)
  Δ₀-pairAt′ k i j = δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∀∈ (δ-∨ δ-≐ δ-≐)))

  Δ₀-prAt′ : {K : Type ℓ} {n : ℕ} (q u v : Fin n) → Δ₀ (prAt′ {K = K} q u v)
  Δ₀-prAt′ q u v = δ-∧ (δ-∃∈ (Δ₀-sglAt′ zero (suc u)))
    (δ-∧ (δ-∃∈ (Δ₀-pairAt′ zero (suc u) (suc v)))
         (δ-∀∈ (δ-∨ (Δ₀-sglAt′ zero (suc u)) (Δ₀-pairAt′ zero (suc u) (suc v)))))

module AtPr {K : Type ℓ} (c : K → V ℓ) where
  module SemK = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemK using ( _^_ )
  open SemK.At K c using ( _⊨_; ⟦_⟧ )

  prAt′-adequate : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
                 → (γ ⊨ prAt′ {K = K} q u v)
                   ≡ ((⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)) , setIsSet _ _)
  prAt′-adequate q u v γ = ⇔toPath
    (λ { (h₁ , h₂ , h₃) → prChar-fwd _ _ _ h₁ h₂ h₃ })
    (λ e → prChar-bwd _ _ _ e)

  prAt′-in : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
           → ⟨ γ ⊨ prAt′ {K = K} q u v ⟩
           → ⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)
  prAt′-in q u v γ h = subst ⟨_⟩ (prAt′-adequate q u v γ) h

  prAt′-out : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
            → ⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)
            → ⟨ γ ⊨ prAt′ {K = K} q u v ⟩
  prAt′-out q u v γ e = subst ⟨_⟩ (sym (prAt′-adequate q u v γ)) e
```

<!--en-->
## The level and the three facts

Fix a limit index. The level is the tower's value there; it is transitive and
closed under the sixteen operations by the step chapter, it is not a member of
itself by regularity, and it is its own union because every member enters at some
stage and that stage's successor level is again a member. Pairing closure is the
ninth operation read through the index, and it is the workhorse of the cases
below.
<!--zh-->
## 层与三条事实

固定一个极限索引。层就是塔在该处的值；由 step 章，它传递且对十六个运算封闭；由正则性，它不属于自身；而它是自身之并，因为每个成员都在某个阶段进场，那个阶段的后继层又是成员。配对封闭即经索引读出的第九个运算，也是下列诸情形的主力。
<!--/-->

```agda
module At (μ : V ℓ) (limμ : ⟨ isLimit μ ⟩) where

  U : V ℓ
  U = Jset μ limμ

  Utr : Transitive 𝒮ᵥ (λ x → x ∈ˢ U)
  Utr = Sset-trans μ

  Urud : (i : Op16) (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ Fof i a b ∈ˢ U ⟩
  Urud = Jset-rud μ limμ

  U∉U : ⟨ U ∈ˢ U ⟩ → Empty.⊥
  U∉U = ∈-irrefl U

  dne : (P : hProp (ℓ-suc ℓ)) → ((⟨ P ⟩ → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
  dne P nn = Sum.rec (λ p → p) (λ np → Empty.rec (nn np)) (lem P)

  prU : (a b : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩ → ⟨ pr a b ∈ˢ U ⟩
  prU a b ha hb = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f9 a b) (Urud op9 a b ha hb)

  prR-in-U : (a b : V ℓ) → ⟨ pr a b ∈ˢ U ⟩ → ⟨ b ∈ˢ U ⟩
  prR-in-U a b h = Utr (F0-spec a b b .snd ∣ inr refl ∣₁)
    (Utr (F9-spec a b (⁅ a , b ⁆) .snd ∣ inr refl ∣₁) h)

  prL-in-U : (a b : V ℓ) → ⟨ pr a b ∈ˢ U ⟩ → ⟨ a ∈ˢ U ⟩
  prL-in-U a b h = Utr (∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd (a∈s a))
    (Utr (F9-spec a b (⁅ a ⁆s) .snd ∣ inl refl ∣₁) h)
    where
    a∈s : (x : V ℓ) → ⟨ x ∈ₛ ⁅ x ⁆s ⟩
    a∈s x = SetPackage.classification (SingletonPackage x) x .snd refl

  Uunion : (x : V ℓ) → ⟨ x ∈ˢ U ⟩
         → ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ˢ U ⟩ × ⟨ x ∈ˢ z ⟩) ∥₁
  Uunion x x∈U = PT.map go (Sset-out μ x x∈U)
    where
    go : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ μ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩)
       → Σ[ z ∈ V ℓ ] (⟨ z ∈ˢ U ⟩ × ⟨ x ∈ˢ z ⟩)
    go (δ , δ∈μ , x∈step) = Sset (sucV δ)
      , ( Sset-mem {α = μ} {β = sucV δ} (limit-succ-mem μ δ limμ δ∈μ)
        , subst (λ t → ⟨ x ∈ˢ t ⟩) (sym (Sset-suc δ)) x∈step )
```

<!--en-->
## The shape of an arm

The switch's image arm is a family of independent obligations, one per operation
and per argument split. Each obligation has the same shape: given that the value
is a subset of the level, produce a formula whose definable subset is that value.
Naming that shape once, `Arm`, lets every case be stated and discharged on its
own, and lets the value be transported along the index equations without ever
touching the sealed dispatch.
<!--zh-->
## 臂的形状

领悟的像臂是一族彼此独立的义务，每个运算、每种实参切分各一条。每条义务同形：给定该值是层的子集，造出一条公式，其可定义子集恰是该值。把这个形状一次命名为 `Arm`，就能让每个情形各自陈述、各自清偿，并让值沿索引方程搬运，全程不碰那个被封的分派。
<!--/-->

```agda
  module Ds = Descr U Utr
  module SemU = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemU.At (⟪ U ⟫) (⟪ U ⟫↪) using ( _⊨_ )

  Split : V ℓ → Type (ℓ-suc ℓ)
  Split a = ⟨ a ∈ˢ U ⟩ ⊎ (a ≡ U)

  splitIn : (a : V ℓ) → Split a → (x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ U ⟩
  splitIn a (inl a∈) x x∈a = Utr x∈a a∈
  splitIn a (inr a≡) x x∈a = subst (λ t → ⟨ x ∈ˢ t ⟩) a≡ x∈a

  Arm : V ℓ → Type (ℓ-suc ℓ)
  Arm W = ((v : V ℓ) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ U ⟩)
        → Σ[ Φ ∈ Formula ⟪ U ⟫ 1 ] (Ds.Defu.defSet Φ ≡ W)

  reshape : {W W' : V ℓ} → W ≡ W' → Arm W' → Arm W
  reshape {W} {W'} e f sub = r .fst , r .snd ∙ sym e
    where
    r : Σ[ Φ ∈ Formula ⟪ U ⟫ 1 ] (Ds.Defu.defSet Φ ≡ W')
    r = f (λ v h → sub v (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym e) h))

  memberArm : (W : V ℓ) → ⟨ W ∈ˢ U ⟩ → Arm W
  memberArm W W∈ sub = Ds.memArm W W∈ sub
```

<!--en-->
## The pair-valued operations

Six of the sixteen always return an unordered pair of two named sets: the pairing
function itself, the Kuratowski pair, and the four tuple operations, whose values
are pairs whatever their arguments are and whether or not the second argument is
a pair. For all six the subset hypothesis does the work: both members of the pair
are members of the level, so the level's closure under pairing puts the value
itself in the level, and the member arm finishes. No argument split is needed and
no junk case arises.
<!--zh-->
## 对值运算

十六个中有六个总是返回两个指名集合的无序对：配对函数自身、Kuratowski 对，以及四个三元组运算，后者不论实参为何、也不论第二实参是否为对，其值都是对。这六个全靠子集假设收工：对的两个成员都是层的成员，故层对配对的封闭把值本身放进层里，成员臂随即完成。既不需要实参分情形，也不产生垃圾情形。
<!--/-->

```agda
  pairArm : (c d : V ℓ) → Arm (F0 c d)
  pairArm c d sub = memberArm (F0 c d) inU sub
    where
    c∈ : ⟨ c ∈ˢ U ⟩
    c∈ = sub c (F0-spec c d c .snd ∣ inl refl ∣₁)
    d∈ : ⟨ d ∈ˢ U ⟩
    d∈ = sub d (F0-spec c d d .snd ∣ inr refl ∣₁)
    inU : ⟨ F0 c d ∈ˢ U ⟩
    inU = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f0 c d) (Urud op0 c d c∈ d∈)
```

<!--en-->
## Difference

The difference is the first place a level parameter does real work. With the
level in the left slot the formula is the negated membership atom against the
right argument, and the level's own members are exactly the candidates the
definable subset ranges over, so the left conjunct of the description chapter's
formula is absorbed. With the level in the right slot the value is empty: the
left argument is a member of the level, hence a subset of it, so nothing survives
the cut.
<!--zh-->
## 差

差是层参数第一次真正出力之处。层在左槽时，公式就是对右实参的否定隶属原子，而层自身的成员恰是可定义子集所遍历的候选，故描述章公式的左合取支被吸收。层在右槽时，值为空：左实参是层的成员，因而是层的子集，切完什么也不剩。
<!--/-->

```agda
  armF1 : (a b : V ℓ) → Split a → Split b → Arm (F1 a b)
  armF1 a b (inl a∈) (inl b∈) sub = memberArm (F1 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f1 a b) (Urud op1 a b a∈ b∈)) sub
  armF1 a b sa (inr b≡) sub = ⊥̇ , Ds.described (F1 a b) ⊥̇ δ-⊥ sub din dout
    where
    din : (v : V ℓ) → ⟨ v ∈ˢ F1 a b ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩
    din v h = Empty.rec (parts .snd
      (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym b≡) (splitIn a sa v (parts .fst))))
      where
      parts : ⟨ v ∈ˢ a ⟩ × (⟨ v ∈ˢ b ⟩ → Empty.⊥)
      parts = F1-spec a b v .fst h
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩ → ⟨ v ∈ˢ F1 a b ⟩
    dout v _ h = Empty.rec* h
  armF1 a b (inr a≡) (inl b∈) sub = Φ , Ds.described (F1 a b) Φ dΦ sub din dout
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ b)
    fib = ∈-asFiber {a = b} {b = U} b∈
    Φ : Formula ⟪ U ⟫ 1
    Φ = ¬̇ (var zero ∈̇ con (fib .fst))
    dΦ : Δ₀ Φ
    dΦ = δ-¬ δ-∈
    din : (v : V ℓ) → ⟨ v ∈ˢ F1 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
    din v h k = F1-spec a b v .fst h .snd
      (subst (λ t → ⟨ v ∈ˢ t ⟩) (fib .snd) k)
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ F1 a b ⟩
    dout v v∈U h = F1-spec a b v .snd
      ( subst (λ t → ⟨ v ∈ˢ t ⟩) (sym a≡) v∈U
      , λ k → h (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym (fib .snd)) k) )
```

<!--en-->
## Union, domain, and the slice

Three operations read only one of their two arguments, and each of them is
absorbed by the level. The union of the level is the level, by the union fact;
the domain of the level is the level, because pairing closure puts the diagonal
pair of every member back inside; and the slice of the level at a member is the
level, for the same reason. When the level sits in the slice's index slot the
value is empty instead, because a pair whose left component is the level would
put the level inside itself.
<!--zh-->
## 并、定义域与切片

有三个运算只读两个实参之一，而它们各自都被层吸收。层之并就是层，由并之事实；层之定义域就是层，因为配对封闭把每个成员的对角对送回其中；层在某个成员处的切片也是层，理由相同。当层坐在切片的索引槽上，值反而为空，因为左分量是层的对会把层放进它自己里面。
<!--/-->

```agda
  armF5 : (a b : V ℓ) → Split a → Arm (F5 a b)
  armF5 a b (inl a∈) sub = memberArm (F5 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f5 a a) (Urud op5 a a a∈ a∈)) sub
  armF5 a b (inr a≡) sub = ⊤̇ , Ds.described (F5 a b) ⊤̇ δ-⊤ sub (λ v _ → tt*) dout
    where
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊤̇ ⟩ → ⟨ v ∈ˢ F5 a b ⟩
    dout v v∈U _ = F5-spec a b v .snd
      (PT.map (λ { (z , z∈U , v∈z) →
         z , ( subst (λ t → ⟨ z ∈ˢ t ⟩) (sym a≡) z∈U , v∈z ) })
        (Uunion v v∈U))

  F6-indep : (a b c : V ℓ) → F6 a b ≡ F6 a c
  F6-indep a b c = extensionality (F6 a b) (F6 a c) (fwd , bwd)
    where
    fwd : ⟨ F6 a b ⊆ F6 a c ⟩
    fwd v h = ∈∈ₛ {a = v} {b = F6 a c} .fst
      (F6-write a c v (F6-read a b v (∈∈ₛ {a = v} {b = F6 a b} .snd h)))
    bwd : ⟨ F6 a c ⊆ F6 a b ⟩
    bwd v h = ∈∈ₛ {a = v} {b = F6 a b} .fst
      (F6-write a b v (F6-read a c v (∈∈ₛ {a = v} {b = F6 a c} .snd h)))

  armF6 : (a b : V ℓ) → Split a → Arm (F6 a b)
  armF6 a b (inl a∈) sub = memberArm (F6 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f6 a a ∙ F6-indep a a b) (Urud op6 a a a∈ a∈))
    sub
  armF6 a b (inr a≡) sub = ⊤̇ , Ds.described (F6 a b) ⊤̇ δ-⊤ sub (λ v _ → tt*) dout
    where
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊤̇ ⟩ → ⟨ v ∈ˢ F6 a b ⟩
    dout v v∈U _ = F6-write a b v ∣ v , v , (pr∈a , refl) ∣₁
      where
      pr∈a : ⟨ pr v v ∈ˢ a ⟩
      pr∈a = subst (λ t → ⟨ pr v v ∈ˢ t ⟩) (sym a≡) (prU v v v∈U v∈U)

  armF10 : (a b : V ℓ) → Split a → Split b → Arm (F10 a b)
  armF10 a b (inl a∈) (inl b∈) sub = memberArm (F10 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f10 a b) (Urud op10 a b a∈ b∈)) sub
  armF10 a b sa (inr b≡) sub = ⊥̇ , Ds.described (F10 a b) ⊥̇ δ-⊥ sub din dout
    where
    din : (v : V ℓ) → ⟨ v ∈ˢ F10 a b ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩
    din v h = Empty.rec (U∉U (subst (λ t → ⟨ t ∈ˢ U ⟩) b≡
      (prL-in-U b v (splitIn a sa (pr b v) (subst ⟨_⟩ (F10-spec a b v) h)))))
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩ → ⟨ v ∈ˢ F10 a b ⟩
    dout v _ h = Empty.rec* h
  armF10 a b (inr a≡) (inl b∈) sub =
    ⊤̇ , Ds.described (F10 a b) ⊤̇ δ-⊤ sub (λ v _ → tt*) dout
    where
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊤̇ ⟩ → ⟨ v ∈ˢ F10 a b ⟩
    dout v v∈U _ = subst ⟨_⟩ (sym (F10-spec a b v))
      (subst (λ t → ⟨ pr b v ∈ˢ t ⟩) (sym a≡) (prU b v b∈ v∈U))
```

<!--en-->
## The relativization slot

The sixteenth operation cuts its argument by the predicate set. At a member
argument the level's closure settles it; at the level itself the value is the
predicate set met with the level, and the formula is the membership atom against
the predicate, which needs the predicate to be named inside the level. That is
the one standing hypothesis of this chapter, and it is the amenability condition
the relativized hierarchy carries anyway: the plain trunk instantiates the slot
at the empty set, a member of every level.
<!--zh-->
## 相对化槽

第十六个运算按谓词集切割其实参。实参为成员时，层的封闭性即可了结；实参为层自身时，值是谓词集与层之交，公式是对谓词的隶属原子，这需要谓词在层内有名字。那正是本章唯一的常驻假设，也是相对化层级本来就携带的可容纳条件：非相对化主干把该槽实例化为空集，而空集是每一层的成员。
<!--/-->

```agda
  module F15U = F15Of A

  armF15 : (a b : V ℓ) → Split a → Split A → Arm (F15A a)
  armF15 a b (inl a∈) hA sub = memberArm (F15A a)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f15 a a) (Urud op15 a a a∈ a∈)) sub
  armF15 a b (inr a≡) (inl A∈) sub =
    Φ , Ds.described (F15A a) Φ dΦ sub din dout
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ A)
    fib = ∈-asFiber {a = A} {b = U} A∈
    Φ : Formula ⟪ U ⟫ 1
    Φ = var zero ∈̇ con (fib .fst)
    dΦ : Δ₀ Φ
    dΦ = δ-∈
    din : (v : V ℓ) → ⟨ v ∈ˢ F15A a ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
    din v h = subst (λ t → ⟨ v ∈ˢ t ⟩) (sym (fib .snd))
      (subst ⟨_⟩ (F15U.F15-spec a v) h .snd)
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ F15A a ⟩
    dout v v∈U h = subst ⟨_⟩ (sym (F15U.F15-spec a v))
      ( subst (λ t → ⟨ v ∈ˢ t ⟩) (sym a≡) v∈U
      , subst (λ t → ⟨ v ∈ˢ t ⟩) (fib .snd) h )
  armF15 a b (inr a≡) (inr A≡) sub =
    ⊤̇ , Ds.described (F15A a) ⊤̇ δ-⊤ sub (λ v _ → tt*) dout
    where
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊤̇ ⟩ → ⟨ v ∈ˢ F15A a ⟩
    dout v v∈U _ = subst ⟨_⟩ (sym (F15U.F15-spec a v))
      ( subst (λ t → ⟨ v ∈ˢ t ⟩) (sym a≡) v∈U
      , subst (λ t → ⟨ v ∈ˢ t ⟩) (sym A≡) v∈U )
```

<!--en-->
## Bounded descent, and the sets of pairs

Two of the sixteen return a set of Kuratowski pairs cut out by a side
condition: the product, and the membership relation restricted to the square of
its first argument. When the level stands in an argument slot the side condition
"the component lies in the level" cannot be written as an atom, because the level
has no constant. It does not need one: a component of a pair is a member of a
member of that pair, so with the candidate ranging over the level's members the
component is in the level by transitivity, for free. The quantifier that used to
be bounded by the argument is therefore re-bound **inside the candidate**, and
the formula stays Δ₀. One frame carries the descent, and each case supplies only
the side condition and its two readings.
<!--zh-->
## 有界下降与对之集

十六个中有两个返回被边条件切出的 Kuratowski 对之集：积，以及限制在第一实参平方上的隶属关系。当层站在某个实参槽上，边条件「分量落在层内」无法写成原子，因为层没有常量。它也不需要：对的分量是该对某个成员的成员，故当候选遍历层的成员时，分量由传递性自动落在层内。原先受实参约束的量词于是改在**候选内部**重新约束，公式仍是 Δ₀。一个框架承载下降，每个情形只供给边条件与它的两种读法。
<!--/-->

```agda
  module PU = AtPr (⟪ U ⟫↪)

  prDescAt : {n : ℕ} → Fin n → Formula ⟪ U ⟫ (suc (suc (suc (suc n))))
           → Formula ⟪ U ⟫ n
  prDescAt k Ψ = ∃̇∈ (var k) (∃̇∈ (var zero) (∃̇∈ (var (suc (suc k)))
                   (∃̇∈ (var zero)
                     (prAt′ (suc (suc (suc (suc k)))) d2 d0 ∧̇ Ψ))))

  Δ₀-prDescAt : {n : ℕ} (k : Fin n) (Ψ : Formula ⟪ U ⟫ (suc (suc (suc (suc n)))))
              → Δ₀ Ψ → Δ₀ (prDescAt k Ψ)
  Δ₀-prDescAt k Ψ dΨ = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
    (δ-∧ (Δ₀-prAt′ (suc (suc (suc (suc k)))) d2 d0) dΨ))))

  PrWitAt : {n : ℕ} (k : Fin n) (Ψ : Formula ⟪ U ⟫ (suc (suc (suc (suc n)))))
          → Vec (V ℓ) n → Type (ℓ-suc ℓ)
  PrWitAt k Ψ γ = Σ[ s ∈ V ℓ ] Σ[ p ∈ V ℓ ] Σ[ t ∈ V ℓ ] Σ[ q ∈ V ℓ ]
                ( ⟨ s ∈ˢ lookup k γ ⟩ × ⟨ p ∈ˢ s ⟩
                × ⟨ t ∈ˢ lookup k γ ⟩ × ⟨ q ∈ˢ t ⟩
                × (lookup k γ ≡ pr p q) × ⟨ (q ∷ t ∷ p ∷ s ∷ γ) ⊨ Ψ ⟩ )

  prDescAt-out : {n : ℕ} (k : Fin n)
                 (Ψ : Formula ⟪ U ⟫ (suc (suc (suc (suc n))))) (γ : Vec (V ℓ) n)
               → ⟨ γ ⊨ prDescAt k Ψ ⟩ → ∥ PrWitAt k Ψ γ ∥₁
  prDescAt-out k Ψ γ = PT.rec PT.squash₁
    (λ { (s , s∈v , h₁) → PT.rec PT.squash₁
    (λ { (p , p∈s , h₂) → PT.rec PT.squash₁
    (λ { (t , t∈v , h₃) → PT.rec PT.squash₁
    (λ { (q , q∈t , hpr , hΨ) →
       ∣ s , p , t , q , ( s∈v , p∈s , t∈v , q∈t
       , PU.prAt′-in (suc (suc (suc (suc k)))) d2 d0 (q ∷ t ∷ p ∷ s ∷ γ) hpr
       , hΨ ) ∣₁ })
    h₃ }) h₂ }) h₁ })

  prDescAt-in : {n : ℕ} (k : Fin n)
                (Ψ : Formula ⟪ U ⟫ (suc (suc (suc (suc n))))) (γ : Vec (V ℓ) n)
                (p q : V ℓ) → (lookup k γ ≡ pr p q)
              → ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ γ) ⊨ Ψ ⟩
              → ⟨ γ ⊨ prDescAt k Ψ ⟩
  prDescAt-in k Ψ γ p q v≡ hΨ =
    ∣ ⁅ p ⁆s , ( sgl∈v , ∣ p , ( p∈sgl , ∣ ⁅ p , q ⁆ , ( pair∈v
    , ∣ q , ( q∈pair
            , ( PU.prAt′-out (suc (suc (suc (suc k)))) d2 d0
                  (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ γ) v≡
              , hΨ ) ) ∣₁ ) ∣₁ ) ∣₁ ) ∣₁
    where
    sgl∈v : ⟨ ⁅ p ⁆s ∈ˢ lookup k γ ⟩
    sgl∈v = subst (λ w → ⟨ ⁅ p ⁆s ∈ˢ w ⟩) (sym v≡)
      (F9-spec p q (⁅ p ⁆s) .snd ∣ inl refl ∣₁)
    p∈sgl : ⟨ p ∈ˢ ⁅ p ⁆s ⟩
    p∈sgl = ∈∈ₛ {a = p} {b = ⁅ p ⁆s} .snd
      (SetPackage.classification (SingletonPackage p) p .snd refl)
    pair∈v : ⟨ ⁅ p , q ⁆ ∈ˢ lookup k γ ⟩
    pair∈v = subst (λ w → ⟨ ⁅ p , q ⁆ ∈ˢ w ⟩) (sym v≡)
      (F9-spec p q (⁅ p , q ⁆) .snd ∣ inr refl ∣₁)
    q∈pair : ⟨ q ∈ˢ ⁅ p , q ⁆ ⟩
    q∈pair = F0-spec p q q .snd ∣ inr refl ∣₁

  prDesc : Formula ⟪ U ⟫ 5 → Formula ⟪ U ⟫ 1
  prDesc Ψ = prDescAt zero Ψ

  Δ₀-prDesc : (Ψ : Formula ⟪ U ⟫ 5) → Δ₀ Ψ → Δ₀ (prDesc Ψ)
  Δ₀-prDesc Ψ dΨ = Δ₀-prDescAt zero Ψ dΨ

  PrWit : (Ψ : Formula ⟪ U ⟫ 5) (v : V ℓ) → Type (ℓ-suc ℓ)
  PrWit Ψ v = PrWitAt zero Ψ (v ∷ [])

  prDesc-out : (Ψ : Formula ⟪ U ⟫ 5) (v : V ℓ)
             → ⟨ (v ∷ []) ⊨ prDesc Ψ ⟩ → ∥ PrWit Ψ v ∥₁
  prDesc-out Ψ v = prDescAt-out zero Ψ (v ∷ [])

  prDesc-in : (Ψ : Formula ⟪ U ⟫ 5) (v p q : V ℓ) → (v ≡ pr p q)
            → ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ Ψ ⟩
            → ⟨ (v ∷ []) ⊨ prDesc Ψ ⟩
  prDesc-in Ψ v p q = prDescAt-in zero Ψ (v ∷ []) p q

  prSetArm : (W : V ℓ) (Ψ : Formula ⟪ U ⟫ 5) → Δ₀ Ψ
           → ((v : V ℓ) → ⟨ v ∈ˢ W ⟩
              → ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ((v ≡ pr p q)
                   × ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ Ψ ⟩) ∥₁)
           → ((v : V ℓ) → ⟨ v ∈ˢ U ⟩ → PrWit Ψ v → ⟨ v ∈ˢ W ⟩)
           → Arm W
  prSetArm W Ψ dΨ read write sub =
    prDesc Ψ , Ds.described W (prDesc Ψ) (Δ₀-prDesc Ψ dΨ) sub din dout
    where
    din : (v : V ℓ) → ⟨ v ∈ˢ W ⟩ → ⟨ (v ∷ []) ⊨ prDesc Ψ ⟩
    din v h = PT.rec (snd ((v ∷ []) ⊨ prDesc Ψ))
      (λ { (p , q , v≡ , hΨ) → prDesc-in Ψ v p q v≡ hΨ }) (read v h)
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ prDesc Ψ ⟩ → ⟨ v ∈ˢ W ⟩
    dout v v∈U h = PT.rec (snd (v ∈ˢ W)) (write v v∈U) (prDesc-out Ψ v h)
```

<!--en-->
The product and the membership relation are then two readings each. In the
product's two mixed cases the surviving side condition is the membership atom for
the argument that is still a member; when both arguments are the level the side
condition is empty. The membership relation reads only its first argument, so it
has one level case, and its side condition is the object-language membership
between the two descended variables.
<!--zh-->
积与隶属关系于是各两种读法。积的两个混合情形里，幸存的边条件是仍为成员的那个实参的隶属原子；两个实参都是层时，边条件为空。隶属关系只读第一实参，故只有一个层情形，其边条件是两个下降变量之间的对象语言隶属。
<!--/-->

```agda
  armF2 : (a b : V ℓ) → Split a → Split b → Arm (F2 a b)
  armF2 a b (inl a∈) (inl b∈) sub = memberArm (F2 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f2 a b) (Urud op2 a b a∈ b∈)) sub
  armF2 a b (inr a≡) (inl b∈) sub = prSetArm (F2 a b) Ψ δ-∈ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ b)
    fib = ∈-asFiber {a = b} {b = U} b∈
    Ψ : Formula ⟪ U ⟫ 5
    Ψ = var d0 ∈̇ con (fib .fst)
    read : (v : V ℓ) → ⟨ v ∈ˢ F2 a b ⟩
         → ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ((v ≡ pr p q)
              × ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ Ψ ⟩) ∥₁
    read v h = PT.map (λ { (p , q , p∈a , q∈b , v≡) →
      p , q , ( v≡ , subst (λ w → ⟨ q ∈ˢ w ⟩) (sym (fib .snd)) q∈b ) })
      (F2-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → PrWit Ψ v → ⟨ v ∈ˢ F2 a b ⟩
    write v v∈U (s , p , t , q , s∈v , p∈s , t∈v , q∈t , v≡ , hΨ) =
      F2-write a b v ∣ p , q
      , ( subst (λ w → ⟨ p ∈ˢ w ⟩) (sym a≡) (Utr p∈s (Utr s∈v v∈U))
        , subst (λ w → ⟨ q ∈ˢ w ⟩) (fib .snd) hΨ , v≡ ) ∣₁
  armF2 a b (inl a∈) (inr b≡) sub = prSetArm (F2 a b) Ψ δ-∈ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ a)
    fib = ∈-asFiber {a = a} {b = U} a∈
    Ψ : Formula ⟪ U ⟫ 5
    Ψ = var d2 ∈̇ con (fib .fst)
    read : (v : V ℓ) → ⟨ v ∈ˢ F2 a b ⟩
         → ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ((v ≡ pr p q)
              × ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ Ψ ⟩) ∥₁
    read v h = PT.map (λ { (p , q , p∈a , q∈b , v≡) →
      p , q , ( v≡ , subst (λ w → ⟨ p ∈ˢ w ⟩) (sym (fib .snd)) p∈a ) })
      (F2-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → PrWit Ψ v → ⟨ v ∈ˢ F2 a b ⟩
    write v v∈U (s , p , t , q , s∈v , p∈s , t∈v , q∈t , v≡ , hΨ) =
      F2-write a b v ∣ p , q
      , ( subst (λ w → ⟨ p ∈ˢ w ⟩) (fib .snd) hΨ
        , subst (λ w → ⟨ q ∈ˢ w ⟩) (sym b≡) (Utr q∈t (Utr t∈v v∈U)) , v≡ ) ∣₁
  armF2 a b (inr a≡) (inr b≡) sub = prSetArm (F2 a b) ⊤̇ δ-⊤ read write sub
    where
    read : (v : V ℓ) → ⟨ v ∈ˢ F2 a b ⟩
         → ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ((v ≡ pr p q)
              × ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ ⊤̇ ⟩) ∥₁
    read v h = PT.map (λ { (p , q , p∈a , q∈b , v≡) → p , q , (v≡ , tt*) })
      (F2-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → PrWit ⊤̇ v → ⟨ v ∈ˢ F2 a b ⟩
    write v v∈U (s , p , t , q , s∈v , p∈s , t∈v , q∈t , v≡ , _) =
      F2-write a b v ∣ p , q
      , ( subst (λ w → ⟨ p ∈ˢ w ⟩) (sym a≡) (Utr p∈s (Utr s∈v v∈U))
        , subst (λ w → ⟨ q ∈ˢ w ⟩) (sym b≡) (Utr q∈t (Utr t∈v v∈U)) , v≡ ) ∣₁

  F7-indep : (a b c : V ℓ) → F7 a b ≡ F7 a c
  F7-indep a b c = extensionality (F7 a b) (F7 a c) (fwd , bwd)
    where
    fwd : ⟨ F7 a b ⊆ F7 a c ⟩
    fwd v h = ∈∈ₛ {a = v} {b = F7 a c} .fst
      (F7-write a c v (F7-read a b v (∈∈ₛ {a = v} {b = F7 a b} .snd h)))
    bwd : ⟨ F7 a c ⊆ F7 a b ⟩
    bwd v h = ∈∈ₛ {a = v} {b = F7 a b} .fst
      (F7-write a b v (F7-read a c v (∈∈ₛ {a = v} {b = F7 a c} .snd h)))

  armF7 : (a b : V ℓ) → Split a → Arm (F7 a b)
  armF7 a b (inl a∈) sub = memberArm (F7 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f7 a a ∙ F7-indep a a b) (Urud op7 a a a∈ a∈))
    sub
  armF7 a b (inr a≡) sub = prSetArm (F7 a b) Ψ δ-∈ read write sub
    where
    Ψ : Formula ⟪ U ⟫ 5
    Ψ = var d2 ∈̇ var d0
    read : (v : V ℓ) → ⟨ v ∈ˢ F7 a b ⟩
         → ∥ Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] ((v ≡ pr p q)
              × ⟨ (q ∷ ⁅ p , q ⁆ ∷ p ∷ ⁅ p ⁆s ∷ v ∷ []) ⊨ Ψ ⟩) ∥₁
    read v h = PT.map (λ { (p , q , p∈a , q∈a , p∈q , v≡) → p , q , (v≡ , p∈q) })
      (F7-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → PrWit Ψ v → ⟨ v ∈ˢ F7 a b ⟩
    write v v∈U (s , p , t , q , s∈v , p∈s , t∈v , q∈t , v≡ , hΨ) =
      F7-write a b v ∣ p , q
      , ( subst (λ w → ⟨ p ∈ˢ w ⟩) (sym a≡) (Utr p∈s (Utr s∈v v∈U))
        , subst (λ w → ⟨ q ∈ˢ w ⟩) (sym a≡) (Utr q∈t (Utr t∈v v∈U))
        , hΨ , v≡ ) ∣₁
```

<!--en-->
## Two descents, for the tuple operations

The two rearrangement operations return right-nested triples: a pair whose right
component is itself a pair. Their descent is the pair descent twice, the second
one relative to the bound variable the first produced, so the frame is the
general one applied at an index rather than at the free variable. The three
components then all lie inside the candidate, hence inside the level, and the two
side conditions the operation imposes are: one component belongs to the first
argument, and one pair of components belongs to the second. The first is an atom
when the argument is a member and vacuous when it is the level; the second is a
bounded existential over the argument when it is a member, and vacuous, by
pairing closure, when it is the level.
<!--zh-->
## 两次下降，为三元组运算而设

两个重排运算返回右嵌套三元组：其右分量本身又是一个对的对。它们的下降就是对下降做两次，第二次相对于第一次产生的约束变量，故框架用的是「在某个序号处」的通用版，而非在自由变量处。三个分量于是都落在候选内部，从而落在层内，而运算施加的两条边条件是：某个分量属于第一实参，某对分量属于第二实参。前者在实参为成员时是原子、在实参为层时自动成立；后者在实参为成员时是对该实参的有界存在，在实参为层时则由配对封闭自动成立。
<!--/-->

```agda
  trDesc : Formula ⟪ U ⟫ 9 → Formula ⟪ U ⟫ 1
  trDesc Ψ = prDescAt zero (prDescAt d0 Ψ)

  Δ₀-trDesc : (Ψ : Formula ⟪ U ⟫ 9) → Δ₀ Ψ → Δ₀ (trDesc Ψ)
  Δ₀-trDesc Ψ dΨ = Δ₀-prDescAt zero (prDescAt d0 Ψ) (Δ₀-prDescAt d0 Ψ dΨ)

  TrWit : (Ψ : Formula ⟪ U ⟫ 9) (v : V ℓ) → Type (ℓ-suc ℓ)
  TrWit Ψ v = Σ[ s ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ t ∈ V ℓ ] Σ[ r ∈ V ℓ ]
              Σ[ s' ∈ V ℓ ] Σ[ c ∈ V ℓ ] Σ[ t' ∈ V ℓ ] Σ[ d ∈ V ℓ ]
              ( ⟨ s ∈ˢ v ⟩ × ⟨ u ∈ˢ s ⟩ × ⟨ t ∈ˢ v ⟩ × ⟨ r ∈ˢ t ⟩
              × (v ≡ pr u r)
              × ⟨ s' ∈ˢ r ⟩ × ⟨ c ∈ˢ s' ⟩ × ⟨ t' ∈ˢ r ⟩ × ⟨ d ∈ˢ t' ⟩
              × (r ≡ pr c d)
              × ⟨ (d ∷ t' ∷ c ∷ s' ∷ r ∷ t ∷ u ∷ s ∷ v ∷ []) ⊨ Ψ ⟩ )

  TrData : (Ψ : Formula ⟪ U ⟫ 9) (v : V ℓ) → Type (ℓ-suc ℓ)
  TrData Ψ v = Σ[ u ∈ V ℓ ] Σ[ c ∈ V ℓ ] Σ[ d ∈ V ℓ ]
      ( (v ≡ pr u (pr c d))
      × ⟨ ( d ∷ ⁅ c , d ⁆ ∷ c ∷ ⁅ c ⁆s ∷ pr c d
          ∷ ⁅ u , pr c d ⁆ ∷ u ∷ ⁅ u ⁆s ∷ v ∷ [] ) ⊨ Ψ ⟩ )

  trDesc-out : (Ψ : Formula ⟪ U ⟫ 9) (v : V ℓ)
             → ⟨ (v ∷ []) ⊨ trDesc Ψ ⟩ → ∥ TrWit Ψ v ∥₁
  trDesc-out Ψ v h =
    PT.rec PT.squash₁ outer (prDescAt-out zero (prDescAt d0 Ψ) (v ∷ []) h)
    where
    outer : PrWitAt zero (prDescAt d0 Ψ) (v ∷ []) → ∥ TrWit Ψ v ∥₁
    outer (s , u , t , r , s∈v , u∈s , t∈v , r∈t , v≡ , hIn) =
      PT.map inner (prDescAt-out d0 Ψ (r ∷ t ∷ u ∷ s ∷ v ∷ []) hIn)
      where
      inner : PrWitAt d0 Ψ (r ∷ t ∷ u ∷ s ∷ v ∷ []) → TrWit Ψ v
      inner (s' , c , t' , d , s'∈r , c∈s' , t'∈r , d∈t' , r≡ , hΨ) =
        s , u , t , r , s' , c , t' , d
        , ( s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡ , hΨ )

  trDesc-in : (Ψ : Formula ⟪ U ⟫ 9) (v u c d : V ℓ) → (v ≡ pr u (pr c d))
            → ⟨ ( d ∷ ⁅ c , d ⁆ ∷ c ∷ ⁅ c ⁆s ∷ pr c d
                ∷ ⁅ u , pr c d ⁆ ∷ u ∷ ⁅ u ⁆s ∷ v ∷ [] ) ⊨ Ψ ⟩
            → ⟨ (v ∷ []) ⊨ trDesc Ψ ⟩
  trDesc-in Ψ v u c d v≡ hΨ =
    prDescAt-in zero (prDescAt d0 Ψ) (v ∷ []) u (pr c d) v≡
      (prDescAt-in d0 Ψ (pr c d ∷ ⁅ u , pr c d ⁆ ∷ u ∷ ⁅ u ⁆s ∷ v ∷ [])
        c d refl hΨ)

  trSetArm : (W : V ℓ) (Ψ : Formula ⟪ U ⟫ 9) → Δ₀ Ψ
           → ((v : V ℓ) → ⟨ v ∈ˢ W ⟩ → ∥ TrData Ψ v ∥₁)
           → ((v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit Ψ v → ⟨ v ∈ˢ W ⟩)
           → Arm W
  trSetArm W Ψ dΨ read write sub =
    trDesc Ψ , Ds.described W (trDesc Ψ) (Δ₀-trDesc Ψ dΨ) sub din dout
    where
    din : (v : V ℓ) → ⟨ v ∈ˢ W ⟩ → ⟨ (v ∷ []) ⊨ trDesc Ψ ⟩
    din v h = PT.rec (snd ((v ∷ []) ⊨ trDesc Ψ))
      (λ { (u , c , d , v≡ , hΨ) → trDesc-in Ψ v u c d v≡ hΨ }) (read v h)
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ trDesc Ψ ⟩ → ⟨ v ∈ˢ W ⟩
    dout v v∈U h = PT.rec (snd (v ∈ˢ W)) (write v v∈U) (trDesc-out Ψ v h)
```

<!--en-->
The two operations differ only in which of the triple's last two components is
tested against the first argument, so their six cases are six pairs of readings
over the same frame.
<!--zh-->
两个运算只差三元组末两个分量中的哪一个对着第一实参受检，故其六个情形就是同一框架上的六对读法。
<!--/-->

```agda
  armF3 : (a b : V ℓ) → Split a → Split b → Arm (F3 a b)
  armF3 a b (inl a∈) (inl b∈) sub = memberArm (F3 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f3 a b) (Urud op3 a b a∈ b∈)) sub
  armF3 a b (inr a≡) (inl b∈) sub = trSetArm (F3 a b) Ψ dΨ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ b)
    fib = ∈-asFiber {a = b} {b = U} b∈
    Ψ : Formula ⟪ U ⟫ 9
    Ψ = ∃̇∈ (con (fib .fst)) (prAt′ d0 d7 d1)
    dΨ : Δ₀ Ψ
    dΨ = δ-∃∈ (Δ₀-prAt′ d0 d7 d1)
    read : (v : V ℓ) → ⟨ v ∈ˢ F3 a b ⟩ → ∥ TrData Ψ v ∥₁
    read v h = PT.map (λ { (u , z , w , z∈a , pr∈b , v≡) →
      u , z , w , ( v≡
      , ∣ pr u w , ( subst (λ y → ⟨ pr u w ∈ˢ y ⟩) (sym (fib .snd)) pr∈b
                   , PU.prAt′-out d0 d7 d1
                       ( pr u w ∷ w ∷ ⁅ z , w ⁆ ∷ z ∷ ⁅ z ⁆s ∷ pr z w
                       ∷ ⁅ u , pr z w ⁆ ∷ u ∷ ⁅ u ⁆s ∷ v ∷ [] ) refl ) ∣₁ ) })
      (F3-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit Ψ v → ⟨ v ∈ˢ F3 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , hΨ ) = PT.rec (snd (v ∈ˢ F3 a b)) go hΨ
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)
      c∈a : ⟨ c ∈ˢ a ⟩
      c∈a = subst (λ w → ⟨ c ∈ˢ w ⟩) (sym a≡) (Utr c∈s' (Utr s'∈r r∈U))
      go : Σ[ y ∈ V ℓ ] ( ⟨ y ∈ˢ ⟪ U ⟫↪ (fib .fst) ⟩
         × ⟨ ( y ∷ d ∷ t' ∷ c ∷ s' ∷ r ∷ t ∷ u ∷ s ∷ v ∷ [] )
             ⊨ prAt′ d0 d7 d1 ⟩ ) → ⟨ v ∈ˢ F3 a b ⟩
      go (y , y∈b , hpr) = F3-write a b v
        ∣ u , c , d , ( c∈a , pr∈b , v≡ ∙ cong (pr u) r≡ ) ∣₁
        where
        y≡ : y ≡ pr u d
        y≡ = PU.prAt′-in d0 d7 d1
               ( y ∷ d ∷ t' ∷ c ∷ s' ∷ r ∷ t ∷ u ∷ s ∷ v ∷ [] ) hpr
        pr∈b : ⟨ pr u d ∈ˢ b ⟩
        pr∈b = subst (λ w → ⟨ w ∈ˢ b ⟩) y≡
          (subst (λ w → ⟨ y ∈ˢ w ⟩) (fib .snd) y∈b)
  armF3 a b (inl a∈) (inr b≡) sub = trSetArm (F3 a b) Ψ δ-∈ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ a)
    fib = ∈-asFiber {a = a} {b = U} a∈
    Ψ : Formula ⟪ U ⟫ 9
    Ψ = var d2 ∈̇ con (fib .fst)
    read : (v : V ℓ) → ⟨ v ∈ˢ F3 a b ⟩ → ∥ TrData Ψ v ∥₁
    read v h = PT.map (λ { (u , z , w , z∈a , pr∈b , v≡) →
      u , z , w , ( v≡ , subst (λ y → ⟨ z ∈ˢ y ⟩) (sym (fib .snd)) z∈a ) })
      (F3-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit Ψ v → ⟨ v ∈ˢ F3 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , hΨ ) = F3-write a b v
      ∣ u , c , d
      , ( subst (λ w → ⟨ c ∈ˢ w ⟩) (fib .snd) hΨ
        , subst (λ w → ⟨ pr u d ∈ˢ w ⟩) (sym b≡)
            (prU u d (Utr u∈s (Utr s∈v v∈U)) (Utr d∈t' (Utr t'∈r r∈U)))
        , v≡ ∙ cong (pr u) r≡ ) ∣₁
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)
  armF3 a b (inr a≡) (inr b≡) sub = trSetArm (F3 a b) ⊤̇ δ-⊤ read write sub
    where
    read : (v : V ℓ) → ⟨ v ∈ˢ F3 a b ⟩ → ∥ TrData ⊤̇ v ∥₁
    read v h = PT.map (λ { (u , z , w , z∈a , pr∈b , v≡) →
      u , z , w , ( v≡ , tt* ) }) (F3-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit ⊤̇ v → ⟨ v ∈ˢ F3 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , _ ) = F3-write a b v
      ∣ u , c , d
      , ( subst (λ w → ⟨ c ∈ˢ w ⟩) (sym a≡) (Utr c∈s' (Utr s'∈r r∈U))
        , subst (λ w → ⟨ pr u d ∈ˢ w ⟩) (sym b≡)
            (prU u d (Utr u∈s (Utr s∈v v∈U)) (Utr d∈t' (Utr t'∈r r∈U)))
        , v≡ ∙ cong (pr u) r≡ ) ∣₁
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)

  armF4 : (a b : V ℓ) → Split a → Split b → Arm (F4 a b)
  armF4 a b (inl a∈) (inl b∈) sub = memberArm (F4 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f4 a b) (Urud op4 a b a∈ b∈)) sub
  armF4 a b (inr a≡) (inl b∈) sub = trSetArm (F4 a b) Ψ dΨ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ b)
    fib = ∈-asFiber {a = b} {b = U} b∈
    Ψ : Formula ⟪ U ⟫ 9
    Ψ = ∃̇∈ (con (fib .fst)) (prAt′ d0 d7 d3)
    dΨ : Δ₀ Ψ
    dΨ = δ-∃∈ (Δ₀-prAt′ d0 d7 d3)
    read : (v : V ℓ) → ⟨ v ∈ˢ F4 a b ⟩ → ∥ TrData Ψ v ∥₁
    read v h = PT.map (λ { (u , w , z , z∈a , pr∈b , v≡) →
      u , w , z , ( v≡
      , ∣ pr u w , ( subst (λ y → ⟨ pr u w ∈ˢ y ⟩) (sym (fib .snd)) pr∈b
                   , PU.prAt′-out d0 d7 d3
                       ( pr u w ∷ z ∷ ⁅ w , z ⁆ ∷ w ∷ ⁅ w ⁆s ∷ pr w z
                       ∷ ⁅ u , pr w z ⁆ ∷ u ∷ ⁅ u ⁆s ∷ v ∷ [] ) refl ) ∣₁ ) })
      (F4-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit Ψ v → ⟨ v ∈ˢ F4 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , hΨ ) = PT.rec (snd (v ∈ˢ F4 a b)) go hΨ
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)
      d∈a : ⟨ d ∈ˢ a ⟩
      d∈a = subst (λ w → ⟨ d ∈ˢ w ⟩) (sym a≡) (Utr d∈t' (Utr t'∈r r∈U))
      go : Σ[ y ∈ V ℓ ] ( ⟨ y ∈ˢ ⟪ U ⟫↪ (fib .fst) ⟩
         × ⟨ ( y ∷ d ∷ t' ∷ c ∷ s' ∷ r ∷ t ∷ u ∷ s ∷ v ∷ [] )
             ⊨ prAt′ d0 d7 d3 ⟩ ) → ⟨ v ∈ˢ F4 a b ⟩
      go (y , y∈b , hpr) = F4-write a b v
        ∣ u , c , d , ( d∈a , pr∈b , v≡ ∙ cong (pr u) r≡ ) ∣₁
        where
        y≡ : y ≡ pr u c
        y≡ = PU.prAt′-in d0 d7 d3
               ( y ∷ d ∷ t' ∷ c ∷ s' ∷ r ∷ t ∷ u ∷ s ∷ v ∷ [] ) hpr
        pr∈b : ⟨ pr u c ∈ˢ b ⟩
        pr∈b = subst (λ w → ⟨ w ∈ˢ b ⟩) y≡
          (subst (λ w → ⟨ y ∈ˢ w ⟩) (fib .snd) y∈b)
  armF4 a b (inl a∈) (inr b≡) sub = trSetArm (F4 a b) Ψ δ-∈ read write sub
    where
    fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ a)
    fib = ∈-asFiber {a = a} {b = U} a∈
    Ψ : Formula ⟪ U ⟫ 9
    Ψ = var d0 ∈̇ con (fib .fst)
    read : (v : V ℓ) → ⟨ v ∈ˢ F4 a b ⟩ → ∥ TrData Ψ v ∥₁
    read v h = PT.map (λ { (u , w , z , z∈a , pr∈b , v≡) →
      u , w , z , ( v≡ , subst (λ y → ⟨ z ∈ˢ y ⟩) (sym (fib .snd)) z∈a ) })
      (F4-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit Ψ v → ⟨ v ∈ˢ F4 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , hΨ ) = F4-write a b v
      ∣ u , c , d
      , ( subst (λ w → ⟨ d ∈ˢ w ⟩) (fib .snd) hΨ
        , subst (λ w → ⟨ pr u c ∈ˢ w ⟩) (sym b≡)
            (prU u c (Utr u∈s (Utr s∈v v∈U)) (Utr c∈s' (Utr s'∈r r∈U)))
        , v≡ ∙ cong (pr u) r≡ ) ∣₁
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)
  armF4 a b (inr a≡) (inr b≡) sub = trSetArm (F4 a b) ⊤̇ δ-⊤ read write sub
    where
    read : (v : V ℓ) → ⟨ v ∈ˢ F4 a b ⟩ → ∥ TrData ⊤̇ v ∥₁
    read v h = PT.map (λ { (u , w , z , z∈a , pr∈b , v≡) →
      u , w , z , ( v≡ , tt* ) }) (F4-read a b v h)
    write : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → TrWit ⊤̇ v → ⟨ v ∈ˢ F4 a b ⟩
    write v v∈U ( s , u , t , r , s' , c , t' , d
                , s∈v , u∈s , t∈v , r∈t , v≡ , s'∈r , c∈s' , t'∈r , d∈t' , r≡
                , _ ) = F4-write a b v
      ∣ u , c , d
      , ( subst (λ w → ⟨ d ∈ˢ w ⟩) (sym a≡) (Utr d∈t' (Utr t'∈r r∈U))
        , subst (λ w → ⟨ pr u c ∈ˢ w ⟩) (sym b≡)
            (prU u c (Utr u∈s (Utr s∈v v∈U)) (Utr c∈s' (Utr s'∈r r∈U)))
        , v≡ ∙ cong (pr u) r≡ ) ∣₁
      where
      r∈U : ⟨ r ∈ˢ U ⟩
      r∈U = Utr r∈t (Utr t∈v v∈U)
```

<!--en-->
## The collection of slices

The collection operation takes one slice of its first argument per member of its
second. With the level in the first slot every slice **is** the level: a pair with
a member of the level on the left and a member on the right is again a member, by
pairing closure, and conversely a pair inside the level has both its components
inside. So the collection is the singleton of the level whenever the second
argument has a member, and then it is not a subset of the level, because the
level is not a member of itself; and when the second argument has no member the
collection is empty. Both readings are the false formula, and no case split is
needed: a member of the collection is the level, and the subset hypothesis makes
that absurd on the spot.

With the level in the **index** slot the collection is instead a member of the
level, so the member arm applies once more, but seeing that costs the chapter's
one classical spend. Slices at indices outside the double union of the first
argument are all empty, hence all equal, so the collection over the whole level
is the collection over the double union, enlarged by at most one point: the
double union is a member of the level (two unions), and so is the singleton of a
witness index with an empty slice, and so is their union. Whether such a witness
exists is decided by the excluded middle at the level of the ambient
propositions, and the two branches name the two sets.
<!--zh-->
## 切片之集

收集运算为第二实参的每个成员取第一实参的一个切片。层在第一槽时，每个切片**就是**层：左边是层的成员、右边也是层的成员的对，由配对封闭仍是成员；反过来，层内的对，两个分量都在层内。于是只要第二实参有成员，收集就是层的单点集，而它不是层的子集，因为层不属于自身；第二实参没有成员时，收集为空。两种读法都是假公式，且无需分情形：收集的成员就是层，子集假设当场令其荒谬。

层坐在**索引**槽上时，收集反而是层的成员，成员臂再次适用，但看清这一点要花掉本章唯一一笔经典支出。索引落在第一实参二重并之外的那些切片全为空，因而彼此相等，于是整个层上的收集就是二重并上的收集，至多再添一个点：二重并是层的成员 (两次并)，某个切片为空的见证索引的单点集也是，二者之并也是。这样的见证是否存在，由环境命题层级上的排中律裁决，两支各自点名一个集合。
<!--/-->

```agda
  sliceU : (z : V ℓ) → ⟨ z ∈ˢ U ⟩ → F10 U z ≡ U
  sliceU z z∈U = extensionality (F10 U z) U (fwd , bwd)
    where
    fwd : ⟨ F10 U z ⊆ U ⟩
    fwd v h = ∈∈ₛ {a = v} {b = U} .fst
      (prR-in-U z v (subst ⟨_⟩ (F10-spec U z v)
        (∈∈ₛ {a = v} {b = F10 U z} .snd h)))
    bwd : ⟨ U ⊆ F10 U z ⟩
    bwd v h = ∈∈ₛ {a = v} {b = F10 U z} .fst
      (subst ⟨_⟩ (sym (F10-spec U z v))
        (prU z v z∈U (∈∈ₛ {a = v} {b = U} .snd h)))

  armF8U : (b : V ℓ) → Split b → Arm (F8 U b)
  armF8U b sb sub = ⊥̇ , Ds.described (F8 U b) ⊥̇ δ-⊥ sub din dout
    where
    din : (v : V ℓ) → ⟨ v ∈ˢ F8 U b ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩
    din v h = Empty.rec (PT.rec Empty.isProp⊥ go (subst ⟨_⟩ (F8-spec U b v) h))
      where
      go : Σ[ m ∈ ⟪ b ⟫ ] (F10 U (⟪ b ⟫↪ m) ≡ v) → Empty.⊥
      go (m , eq) = U∉U (subst (λ w → ⟨ w ∈ˢ U ⟩)
        (sym eq ∙ sliceU (⟪ b ⟫↪ m)
          (splitIn b sb (⟪ b ⟫↪ m)
            (∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd (∈ₛ⟪ b ⟫↪ m))))
        (sub v h))
    dout : (v : V ℓ) → ⟨ v ∈ˢ U ⟩ → ⟨ (v ∷ []) ⊨ ⊥̇ ⟩ → ⟨ v ∈ˢ F8 U b ⟩
    dout v _ h = Empty.rec* h

  binU : V ℓ → V ℓ → V ℓ
  binU x y = F5 (F0 x y) (F0 x y)

  binU∈U : (x y : V ℓ) → ⟨ x ∈ˢ U ⟩ → ⟨ y ∈ˢ U ⟩ → ⟨ binU x y ∈ˢ U ⟩
  binU∈U x y hx hy = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f5 (F0 x y) (F0 x y))
    (Urud op5 (F0 x y) (F0 x y) h₀ h₀)
    where
    h₀ : ⟨ F0 x y ∈ˢ U ⟩
    h₀ = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f0 x y) (Urud op0 x y hx hy)

  binU-inl : (x y v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ binU x y ⟩
  binU-inl x y v h = F5-spec (F0 x y) (F0 x y) v .snd
    ∣ x , (F0-spec x y x .snd ∣ inl refl ∣₁ , h) ∣₁

  binU-inr : (x y v : V ℓ) → ⟨ v ∈ˢ y ⟩ → ⟨ v ∈ˢ binU x y ⟩
  binU-inr x y v h = F5-spec (F0 x y) (F0 x y) v .snd
    ∣ y , (F0-spec x y y .snd ∣ inr refl ∣₁ , h) ∣₁

  binU∈U-mem : (x y v : V ℓ) → ⟨ x ∈ˢ U ⟩ → ⟨ y ∈ˢ U ⟩
             → ⟨ v ∈ˢ binU x y ⟩ → ⟨ v ∈ˢ U ⟩
  binU∈U-mem x y v hx hy h = Utr h (binU∈U x y hx hy)

  dblU : V ℓ → V ℓ
  dblU a = F5 (F5 a a) (F5 a a)

  dblU∈U : (a : V ℓ) → ⟨ a ∈ˢ U ⟩ → ⟨ dblU a ∈ˢ U ⟩
  dblU∈U a a∈ = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f5 (F5 a a) (F5 a a))
    (Urud op5 (F5 a a) (F5 a a) h₅ h₅)
    where
    h₅ : ⟨ F5 a a ∈ˢ U ⟩
    h₅ = subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f5 a a) (Urud op5 a a a∈ a∈)

  F8-ext : (a c c' : V ℓ)
         → ((z : V ℓ) → ⟨ z ∈ˢ c ⟩
            → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ c' ⟩ × (F10 a z ≡ F10 a y)) ∥₁)
         → ((z : V ℓ) → ⟨ z ∈ˢ c' ⟩
            → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ c ⟩ × (F10 a z ≡ F10 a y)) ∥₁)
         → F8 a c ≡ F8 a c'
  F8-ext a c c' fwd bwd = extensionality (F8 a c) (F8 a c') (sub₁ , sub₂)
    where
    move : (e e' : V ℓ)
         → ((z : V ℓ) → ⟨ z ∈ˢ e ⟩
            → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ e' ⟩ × (F10 a z ≡ F10 a y)) ∥₁)
         → ⟨ F8 a e ⊆ F8 a e' ⟩
    move e e' step w h = ∈∈ₛ {a = w} {b = F8 a e'} .fst
      (subst ⟨_⟩ (sym (F8-spec a e' w))
        (PT.rec (snd (w ∈ˢ F8 a e')) go
          (subst ⟨_⟩ (F8-spec a e w) (∈∈ₛ {a = w} {b = F8 a e} .snd h))))
      where
      go : Σ[ m ∈ ⟪ e ⟫ ] (F10 a (⟪ e ⟫↪ m) ≡ w) → ⟨ w ∈ˢ F8 a e' ⟩
      go (m , eq) = PT.rec (snd (w ∈ˢ F8 a e')) go'
        (step (⟪ e ⟫↪ m)
          (∈∈ₛ {a = ⟪ e ⟫↪ m} {b = e} .snd (∈ₛ⟪ e ⟫↪ m)))
        where
        go' : Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ e' ⟩ × (F10 a (⟪ e ⟫↪ m) ≡ F10 a y))
            → ⟨ w ∈ˢ F8 a e' ⟩
        go' (y , y∈e' , sl≡) = subst ⟨_⟩ (sym (F8-spec a e' w))
          ∣ fib .fst , cong (F10 a) (fib .snd) ∙ sym sl≡ ∙ eq ∣₁
          where
          fib : Σ[ m' ∈ ⟪ e' ⟫ ] (⟪ e' ⟫↪ m' ≡ y)
          fib = ∈-asFiber {a = y} {b = e'} y∈e'
    sub₁ : ⟨ F8 a c ⊆ F8 a c' ⟩
    sub₁ = move c c' fwd
    sub₂ : ⟨ F8 a c' ⊆ F8 a c ⟩
    sub₂ = move c' c bwd

  emptySlice≡ : (a z y : V ℓ)
              → ((v : V ℓ) → ⟨ v ∈ˢ F10 a z ⟩ → Empty.⊥)
              → ((v : V ℓ) → ⟨ v ∈ˢ F10 a y ⟩ → Empty.⊥)
              → F10 a z ≡ F10 a y
  emptySlice≡ a z y e e' = extensionality (F10 a z) (F10 a y)
    ( (λ v h → Empty.rec (e v (∈∈ₛ {a = v} {b = F10 a z} .snd h)))
    , (λ v h → Empty.rec (e' v (∈∈ₛ {a = v} {b = F10 a y} .snd h))) )

  Inhab : V ℓ → V ℓ → hProp (ℓ-suc ℓ)
  Inhab a z = ∥ Σ[ v ∈ V ℓ ] ⟨ v ∈ˢ F10 a z ⟩ ∥₁ , PT.squash₁

  inhab→dbl : (a z : V ℓ) → ⟨ Inhab a z ⟩ → ⟨ z ∈ˢ dblU a ⟩
  inhab→dbl a z = PT.rec (snd (z ∈ˢ dblU a))
    (λ { (v , h) → prL-in-doubleUnion a z v (subst ⟨_⟩ (F10-spec a z v) h) })

  armF8I : (a : V ℓ) → ⟨ a ∈ˢ U ⟩ → Arm (F8 a U)
  armF8I a a∈ sub = memberArm (F8 a U) inU sub
    where
    dbl∈ : ⟨ dblU a ∈ˢ U ⟩
    dbl∈ = dblU∈U a a∈
    caseFull : (( z : V ℓ) → ⟨ z ∈ˢ U ⟩ → ⟨ Inhab a z ⟩) → ⟨ F8 a U ∈ˢ U ⟩
    caseFull full = subst (λ t → ⟨ t ∈ˢ U ⟩) (sym eq)
      (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f8 a (dblU a)) (Urud op8 a (dblU a) a∈ dbl∈))
      where
      eq : F8 a U ≡ F8 a (dblU a)
      eq = F8-ext a U (dblU a)
        (λ z z∈U → ∣ z , (inhab→dbl a z (full z z∈U) , refl) ∣₁)
        (λ z z∈d → ∣ z , (Utr z∈d dbl∈ , refl) ∣₁)
    caseGap : (z₀ : V ℓ) → ⟨ z₀ ∈ˢ U ⟩ → (⟨ Inhab a z₀ ⟩ → Empty.⊥)
            → ⟨ F8 a U ∈ˢ U ⟩
    caseGap z₀ z₀∈U nz₀ = subst (λ t → ⟨ t ∈ˢ U ⟩) (sym eq)
      (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f8 a c) (Urud op8 a c a∈ c∈))
      where
      c : V ℓ
      c = binU (dblU a) (F0 z₀ z₀)
      c∈ : ⟨ c ∈ˢ U ⟩
      c∈ = binU∈U (dblU a) (F0 z₀ z₀) dbl∈
        (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f0 z₀ z₀) (Urud op0 z₀ z₀ z₀∈U z₀∈U))
      z₀∈c : ⟨ z₀ ∈ˢ c ⟩
      z₀∈c = binU-inr (dblU a) (F0 z₀ z₀) z₀ (F0-spec z₀ z₀ z₀ .snd ∣ inl refl ∣₁)
      fwd : (z : V ℓ) → ⟨ z ∈ˢ U ⟩
          → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ c ⟩ × (F10 a z ≡ F10 a y)) ∥₁
      fwd z z∈U = go (lem (Inhab a z))
        where
        go : (⟨ Inhab a z ⟩ ⊎ (⟨ Inhab a z ⟩ → Empty.⊥))
           → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ c ⟩ × (F10 a z ≡ F10 a y)) ∥₁
        go (inl hz) = ∣ z , ( binU-inl (dblU a) (F0 z₀ z₀) z (inhab→dbl a z hz)
                            , refl ) ∣₁
        go (inr nz) = ∣ z₀ , ( z₀∈c
          , emptySlice≡ a z z₀ (λ v h → nz ∣ v , h ∣₁)
              (λ v h → nz₀ ∣ v , h ∣₁) ) ∣₁
      bwd : (z : V ℓ) → ⟨ z ∈ˢ c ⟩
          → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ˢ U ⟩ × (F10 a z ≡ F10 a y)) ∥₁
      bwd z z∈c = ∣ z
        , ( binU∈U-mem (dblU a) (F0 z₀ z₀) z dbl∈
              (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f0 z₀ z₀)
                (Urud op0 z₀ z₀ z₀∈U z₀∈U)) z∈c
          , refl ) ∣₁
      eq : F8 a U ≡ F8 a c
      eq = F8-ext a U c fwd bwd
    Gap : hProp (ℓ-suc ℓ)
    Gap = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ˢ U ⟩ × (⟨ Inhab a z ⟩ → Empty.⊥)) ∥₁
        , PT.squash₁
    fromGap : ⟨ Gap ⟩ → ⟨ F8 a U ∈ˢ U ⟩
    fromGap = PT.rec (snd (F8 a U ∈ˢ U))
      (λ { (z₀ , z₀∈U , nz₀) → caseGap z₀ z₀∈U nz₀ })
    noGap : (⟨ Gap ⟩ → Empty.⊥) → ⟨ F8 a U ∈ˢ U ⟩
    noGap ng = caseFull
      (λ z z∈U → dne (Inhab a z) (λ n → ng ∣ z , (z∈U , n) ∣₁))
    inU : ⟨ F8 a U ∈ˢ U ⟩
    inU = Sum.rec fromGap noGap (lem Gap)

  armF8 : (a b : V ℓ) → Split a → Split b → Arm (F8 a b)
  armF8 a b (inl a∈) (inl b∈) sub = memberArm (F8 a b)
    (subst (λ t → ⟨ t ∈ˢ U ⟩) (Fof-f8 a b) (Urud op8 a b a∈ b∈)) sub
  armF8 a b (inl a∈) (inr b≡) sub =
    reshape (cong (F8 a) b≡) (armF8I a a∈) sub
  armF8 a b (inr a≡) sb sub =
    reshape (cong (λ w → F8 w b) a≡) (armF8U b sb) sub
```

<!--en-->
## The dispatch

With the arms in hand the image arm is a sixteen-way dispatch, each case
transported along its index equation. All sixteen are discharged; the module's
only hypothesis is that the relativization slot is named inside the level, which
the sixteenth operation's level case needs and nothing else does.
<!--zh-->
## 分派

诸臂在手，像臂就是一场十六路分派，每个情形沿其索引方程搬运。十六个全部清偿；本模块唯一的假设是相对化槽在层内有名字，那是第十六个运算的层情形所需，此外别无所求。
<!--/-->

```agda
  module ImgArmOf
    (hA : Split A)
    where

    imgArm : Ds.ImgArm
    imgArm op0 a b sa sb = reshape (Fof-f0 a b) (pairArm a b)
    imgArm op1 a b sa sb = reshape (Fof-f1 a b) (armF1 a b sa sb)
    imgArm op2 a b sa sb = reshape (Fof-f2 a b) (armF2 a b sa sb)
    imgArm op3 a b sa sb = reshape (Fof-f3 a b) (armF3 a b sa sb)
    imgArm op4 a b sa sb = reshape (Fof-f4 a b) (armF4 a b sa sb)
    imgArm op5 a b sa sb = reshape (Fof-f5 a b) (armF5 a b sa)
    imgArm op6 a b sa sb = reshape (Fof-f6 a b) (armF6 a b sa)
    imgArm op7 a b sa sb = reshape (Fof-f7 a b) (armF7 a b sa)
    imgArm op8 a b sa sb = reshape (Fof-f8 a b) (armF8 a b sa sb)
    imgArm op9 a b sa sb = reshape (Fof-f9 a b) (pairArm (⁅ a ⁆s) (⁅ a , b ⁆))
    imgArm op10 a b sa sb = reshape (Fof-f10 a b) (armF10 a b sa sb)
    imgArm op11 a b sa sb = reshape (Fof-f11 a b)
      (pairArm (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆))
    imgArm op12 a b sa sb = reshape (Fof-f12 a b)
      (pairArm (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆))
    imgArm op13 a b sa sb = reshape (Fof-f13 a b)
      (pairArm (left b) (pr (right b) a))
    imgArm op14 a b sa sb = reshape (Fof-f14 a b)
      (pairArm (left b) (pr a (right b)))
    imgArm op15 a b sa sb = reshape (Fof-f15 a b) (armF15 a b sa hA)
```

<!--en-->
## The lift up the tower

The switch's subset direction is stated at one application of the operator. The
tower lift asks it at a stage, and the stage recursion supplies the shape: a
member of the level at index `δ` enters at some earlier index `γ`, inside one
step over the level there. Two things can then happen. If `γ` is below the limit
the whole step is absorbed: the next level is still below the limit, so the
member is already a member of `U`, and a member of a transitive set is definable
over it by the atom. If `γ` is the limit itself, the member sits in one step over
`U`, which is exactly what the one-step statement handles. The hypothesis that
makes the two cases exhaustive is that the stage is bounded by the successor of
the limit, written here as "every index below the stage is below the limit or is
the limit".

That bound is not a convenience: past it the statement is **false**. A subset of
`U` appearing two blocks up is definable over the level one block up, and by
Tarski's theorem that is strictly more than what is definable over `U` (the
satisfaction predicate of `U` is the standard witness). So the target of the lift
is the block, not an arbitrary limit above.
<!--zh-->
## 沿塔的提升

领悟的子集方向陈述在算子的一次施用处。塔的提升在某个阶段处发问，而阶段递归给出形状：索引 `δ` 处那层的成员在某个更早的索引 `γ` 处进场，落在那里的层之上一步内。接下来只有两种可能。若 `γ` 在极限之下，整一步被吸收：下一层仍在极限之下，故该成员早已是 `U` 的成员，而传递集的成员经原子在其上可定义。若 `γ` 就是那个极限，该成员坐在 `U` 之上一步内，恰是单步陈述所处理者。使两情形穷尽的假设，是阶段被极限的后继所界，此处写作「阶段以下的每个索引，要么在极限之下，要么就是那个极限」。

这道界并非图方便：越过它，陈述就是**假的**。再上两块出现的 `U` 的子集在上一块那层上可定义，而由 Tarski 定理，那严格多于在 `U` 上可定义者 (标准见证就是 `U` 的满足谓词)。故提升的目标是那一块，而不是其上任意一个极限。
<!--/-->

```agda
    memberDef : (x : V ℓ) → ⟨ x ∈ˢ U ⟩
              → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ U ⟩)
              → ⟨ x ∈ˢ Ds.Defu.Def ⟩
    memberDef x x∈U sub = ∣ r .fst , r .snd ∣₁
      where
      r : Σ[ Φ ∈ Formula ⟪ U ⟫ 1 ] (Ds.Defu.defSet Φ ≡ x)
      r = Ds.memArm x x∈U sub

    stepDef : (x : V ℓ) → ⟨ x ∈ˢ step U ⟩
            → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ U ⟩)
            → ⟨ x ∈ˢ Ds.Defu.Def ⟩
    stepDef = Ds.switch-⊆ imgArm

    belowDef : (γ : V ℓ) → ⟨ γ ∈ˢ μ ⟩ → (x : V ℓ) → ⟨ x ∈ˢ step (Sset γ) ⟩
             → ⟨ x ∈ˢ U ⟩
    belowDef γ γ∈μ x h =
      Sset-mono {α = μ} {β = sucV γ} (limit-succ-mem μ γ limμ γ∈μ) x
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc γ)) h)

    towerDef : (δ : V ℓ)
             → ((γ : V ℓ) → ⟨ γ ∈ˢ δ ⟩ → (⟨ γ ∈ˢ μ ⟩ ⊎ (γ ≡ μ)))
             → (x : V ℓ) → ⟨ x ∈ˢ Sset δ ⟩
             → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ U ⟩)
             → ⟨ x ∈ˢ Ds.Defu.Def ⟩
    towerDef δ bound x x∈ sub =
      PT.rec (snd (x ∈ˢ Ds.Defu.Def)) go (Sset-out δ x x∈)
      where
      atStage : (γ : V ℓ) → (⟨ γ ∈ˢ μ ⟩ ⊎ (γ ≡ μ)) → ⟨ x ∈ˢ step (Sset γ) ⟩
              → ⟨ x ∈ˢ Ds.Defu.Def ⟩
      atStage γ (inl γ∈μ) h = memberDef x (belowDef γ γ∈μ x h) sub
      atStage γ (inr γ≡μ) h =
        stepDef x (subst (λ w → ⟨ x ∈ˢ step w ⟩) (cong Sset γ≡μ) h) sub
      go : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ˢ δ ⟩ × ⟨ x ∈ˢ step (Sset γ) ⟩)
         → ⟨ x ∈ˢ Ds.Defu.Def ⟩
      go (γ , γ∈δ , h) = atStage γ (bound γ γ∈δ) h
```

<!--en-->
## The improved corollary

The switch chapter's limit corollary takes the image arm as a hypothesis on the
subset direction. Here it is discharged, so the same statement stands with three
fewer hypotheses on the operations side and one more fact on the tower side: the
level's rud closure, which the step chapter proves. The stage version is the new
export, and the one-step version is the old statement with its hypothesis gone.
Nothing in the switch chapter changes.
<!--zh-->
## 改进的推论

领悟章的极限推论在子集方向上取像臂为假设。此处它已清偿，故同一陈述在运算一侧少了三条假设、在塔一侧多了一条事实：层的初步闭包，由 step 章证出。阶段版是新的导出，单步版就是旧陈述去掉其假设之后的样子。领悟章分毫未动。
<!--/-->

```agda
    closure→definable : (x : V ℓ) → ⟨ x ∈ˢ step U ⟩
                      → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ U ⟩)
                      → ⟨ x ∈ˢ Ds.Defu.Def ⟩
    closure→definable = stepDef

    closure→definable-tower : (δ : V ℓ)
                            → ((γ : V ℓ) → ⟨ γ ∈ˢ δ ⟩ → (⟨ γ ∈ˢ μ ⟩ ⊎ (γ ≡ μ)))
                            → (x : V ℓ) → ⟨ x ∈ˢ Sset δ ⟩
                            → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ U ⟩)
                            → ⟨ x ∈ˢ Ds.Defu.Def ⟩
    closure→definable-tower = towerDef
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The image arm of the switch theorem is discharged at every limit level of the
tower, with one hypothesis: the relativization slot is named inside the level.
Three facts about a level carry the whole chapter. Its closure under the sixteen
operations makes every plain-argument value a member of the level, so the member
arm applies and the bulky per-operation instantiation the description chapter
would have needed never happens. Its irreflexivity kills the cases where the
value would have to contain the level. Its being its own union, together with
pairing closure, collapses the union, the domain, and the slice at a member to
the level itself, described by the true formula.

What is left is exactly the classical content: the product, the membership
relation, and the two tuple rearrangements at a level parameter. Those are
described by bounded descent, and this is where the chapter departs from the
textbook. SZ's Lemma 1.4 lands in `Σ_ω` over the level because a transitive
carrier gives no way to bound the quantifier that ranged over the parameter. At a
level the quantifier need not be bounded by the parameter at all: the component
it binds sits inside the candidate, two or four membership steps down, and the
candidate ranges over the level. Every formula this chapter produces is therefore
**Δ₀**, not merely first-order, and relativization is never invoked.

The tower lift is the stage recursion with the two outcomes the stage split
allows: absorption below the limit, and the one-step statement at the limit. Its
bound is the successor of the limit index, and that bound is sharp: past it the
statement fails by Tarski's theorem.
<!--zh-->
领悟定理的像臂在塔的每个极限层处清偿，只带一条假设：相对化槽在层内有名字。关于层的三条事实撑起了整章。它对十六个运算的封闭性使每个平实参之值都是层的成员，于是成员臂适用，描述章本会需要的那场笨重的逐运算实例化根本没有发生。它的非自反性杀掉了那些值本该含有层的情形。它是自身之并，连同配对封闭，把并、定义域以及在成员处的切片一齐坍缩为层自身，用真公式描述。

剩下的恰是经典内容：积、隶属关系，以及层参数处的两个三元组重排。它们由有界下降描述，而本章正是在此偏离教科书。SZ 引理 1.4 落在层上的 `Σ_ω` 里，因为传递载体无从界住那个原本遍历参数的量词。在层处，那个量词根本不必由参数来界：它所约束的分量就坐在候选内部，往下两步或四步，而候选遍历该层。故本章产出的每条公式都是 **Δ₀**，而不只是一阶，相对化自始至终未被调用。

塔的提升就是阶段递归，加上阶段切分所允许的两种结局：极限之下被吸收，极限处即单步陈述。它的界是极限索引的后继，而这道界是紧的：越过它，由 Tarski 定理陈述即失效。
<!--/-->
