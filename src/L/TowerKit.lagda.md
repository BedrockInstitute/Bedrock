# The constructible tower's kit for the rud step

<!--en-->
The rud step's values land in the constructible tower. This chapter hosts the
standing facts that reading needs, at the tower itself: the two-way inclusion
principle of set equality, the stage transitivity, the Def-step offset, the
pairing offset, the sixteen values inside one stage, and the four-step index
alias the reduction reads. The pairing description lives here in its
layer-free form, so the pairing arm also serves the consumers below the graph
layer.
<!--zh-->
初步函数一步的值落在可构造塔里。本章在塔本身处收存那次读取所需的存量事实：集合等式的双向包含原则、阶段的传递性、Def 步的偏移、配对的偏移、十六个值落进一个阶段，以及归约所读的四步索引别名。配对描述以无图层的形式住在这里，故配对臂同样服务于图层之下的消费方。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.TowerKit {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; _∨̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using
  ( isTransV; Lset; Lset-in; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( module PairKit )
open import L.Rud.Ops {ℓ} using ( F0; F0-spec )
open import L.Rud.Step {ℓ} lem A using ( Op16; Fof )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData.Base using ( Fin; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Set extensionality

The kit opens with the cumulative hierarchy's own equality principle. Two
sets are equal when each is a subset of the other: `ext-⊆`{.Agda} names that
principle at the small membership, and `empty-⊆`{.Agda} reads the empty set's
defining property through it. Every `defSet` equation below closes with these
two inclusions.
<!--zh-->
## 集合外延性

套件以累积层级自己的等式原则开场。两个集合相等，当且仅当彼此互为一个的子集：`ext-⊆`{.Agda} 在小隶属处点名这条原则，`empty-⊆`{.Agda} 经由它读出空集的定义性。以下每条 `defSet` 等式都以此两条包含收口。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

empty-⊆ : (u : S) → ((x : S) → ⟨ x ∈ˢ u ⟩ → Empty.⊥) → u ≡ ∅
empty-⊆ u no = ext-⊆ (λ x h → Empty.rec (no x h))
  (λ x h → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h)))
```

<!--en-->
## The stage offsets

The rud step reads the tower at two offsets. Every stage is transitive, so a
member that a value's description needs is already in the stage that holds
the value. And a definable subset of a stage lands in the next stage, which
is the single offset every value's description consumes.
<!--zh-->
## 阶段的偏移

初步函数步在塔处读两处偏移。每个阶段都是传递的，故一个值的描述所需的成员，早已落在收下该值的阶段里。而一个阶段的可定义子集落进下一阶段，这正是每条值描述所消费的那一条偏移。
<!--/-->

```agda
Ltr : (ξ : S) → Transitive 𝒮ᵥ (λ x → x ∈ˢ Lset ξ)
Ltr ξ = layer-trans (Lset-layer ξ)

𝒟ₒ⊆Lsuc : (ξ x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset ξ) ⟩ → ⟨ x ∈ˢ Lset (sucV ξ) ⟩
𝒟ₒ⊆Lsuc ξ x h = Lset-in (sucV ξ) ξ x (self∈sucV ξ) h
```

<!--en-->
## The pairing description, without the layer

Pairing is the one arm that the graph layer's consumer below the layer reads.
The module `F0Arm`{.Agda} describes the pair `F0 p q` at any transitive
carrier that holds `p` and `q`: the formula forces the two argument slots to
the carrier fibers, re-connects the member slot to the free tail variable,
and the pairing membership is an equality disjunction, so no graph-layer
machinery enters. The equation is closed: every member of a pair is one of
the two arguments, so the caller supplies no subset certificate.
<!--zh-->
## 配对描述，不带图层

配对是图层之下的消费方所读的那条臂。模块 `F0Arm`{.Agda} 在收下 `p` 与 `q` 的任意传递载体处描述对 `F0 p q`：公式把两个实参槽固定到载体的纤维，把成员槽重新接到自由的尾部变量，而配对隶属是一道等式析取，故任何图层机制都不进场。等式是封闭的：对的每个成员都是两个实参之一，故调用方无需供应子集证书。
<!--/-->

```agda
module F0Arm (C : S) (Ctr : isTransV C) (p q : S)
             (p∈ : ⟨ p ∈ˢ C ⟩) (q∈ : ⟨ q ∈ˢ C ⟩) where

  module DefC = DefOf C
  open DefC using ( SM; ι; _⊨ᵐ_; defSet ) public
  module PK = PairKit C Ctr

  private
    f0 : {n : ℕ} → Fin (suc n)
    f0 = zero
    f1 : {n : ℕ} → Fin (suc (suc n))
    f1 = suc f0
    f2 : {n : ℕ} → Fin (suc (suc (suc n)))
    f2 = suc f1
    f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    f3 = suc f2

  mₐ : ⟪ C ⟫
  mₐ = ∈-asFiber {a = p} {b = C} p∈ .fst
  qₐ : ⟪ C ⟫↪ mₐ ≡ p
  qₐ = ∈-asFiber {a = p} {b = C} p∈ .snd
  m_b : ⟪ C ⟫
  m_b = ∈-asFiber {a = q} {b = C} q∈ .fst
  q_b : ⟪ C ⟫↪ m_b ≡ q
  q_b = ∈-asFiber {a = q} {b = C} q∈ .snd

  -- The pinned pairing formula: the member slot re-pinned to the free tail
  -- variable, the two argument slots pinned to the carrier fibers, and the
  -- pairing membership (an equality disjunction) at the bound member.
  body : Formula ⟪ C ⟫ 4
  body = (var f0 ≐ var f3) ∧̇
    ((var f1 ≐ con m_b) ∧̇ ((var f2 ≐ con mₐ) ∧̇
      ((var f0 ≐ var f2) ∨̇ (var f0 ≐ var f1))))

  pinned : Formula ⟪ C ⟫ 1
  pinned = ∃̇ (∃̇ (∃̇ body))

  pinned-out : (m : ⟪ C ⟫)
             → ⟨ (ι m ∷ []) ⊨ᵐ pinned ⟩ → ⟨ ⟪ C ⟫↪ m ∈ˢ F0 p q ⟩
  pinned-out m h = PT.rec (snd (⟪ C ⟫↪ m ∈ˢ F0 p q)) k2 h
    where
    k2 : Σ[ x₂ ∈ SM ] ⟨ (x₂ ∷ ι m ∷ []) ⊨ᵐ (∃̇ (∃̇ body)) ⟩
       → ⟨ ⟪ C ⟫↪ m ∈ˢ F0 p q ⟩
    k2 (x₂ , h₂) = PT.rec (snd (⟪ C ⟫↪ m ∈ˢ F0 p q)) k1 h₂
      where
      k1 : Σ[ x₁ ∈ SM ] ⟨ (x₁ ∷ x₂ ∷ ι m ∷ []) ⊨ᵐ (∃̇ body) ⟩
         → ⟨ ⟪ C ⟫↪ m ∈ˢ F0 p q ⟩
      k1 (x₁ , h₁) = PT.rec (snd (⟪ C ⟫↪ m ∈ˢ F0 p q)) k0 h₁
        where
        k0 : Σ[ x₀ ∈ SM ] ⟨ (x₀ ∷ x₁ ∷ x₂ ∷ ι m ∷ []) ⊨ᵐ body ⟩
           → ⟨ ⟪ C ⟫↪ m ∈ˢ F0 p q ⟩
        k0 (x₀ , h₀) = subst (λ w → ⟨ w ∈ˢ F0 p q ⟩) p0
          (subst (λ t → ⟨ fst x₀ ∈ˢ F0 p t ⟩) (p1 ∙ q_b)
            (subst (λ t → ⟨ fst x₀ ∈ˢ F0 t (fst x₁) ⟩) (p2 ∙ qₐ) z∈F))
          where
          p0 : fst x₀ ≡ ⟪ C ⟫↪ m
          p0 = h₀ .fst
          p1 : fst x₁ ≡ ⟪ C ⟫↪ m_b
          p1 = h₀ .snd .fst
          p2 : fst x₂ ≡ ⟪ C ⟫↪ mₐ
          p2 = h₀ .snd .snd .fst
          z∈F : ⟨ fst x₀ ∈ˢ F0 (fst x₂) (fst x₁) ⟩
          z∈F = F0-spec (fst x₂) (fst x₁) (fst x₀) .snd (h₀ .snd .snd .snd)

  pinned-in : (m : ⟪ C ⟫)
            → ⟨ ⟪ C ⟫↪ m ∈ˢ F0 p q ⟩ → ⟨ (ι m ∷ []) ⊨ᵐ pinned ⟩
  pinned-in m h =
    ∣ PK.pt p p∈ , (∣ PK.pt q q∈ , (∣ ι m , (pin₀ , (pin₁ , (pin₂ , ms))) ∣₁) ∣₁) ∣₁
    where
    pin₀ : ⟨ (ι m ∷ PK.pt q q∈ ∷ PK.pt p p∈ ∷ ι m ∷ [])
             ⊨ᵐ (var f0 ≐ var f3) ⟩
    pin₀ = refl
    pin₁ : ⟨ (ι m ∷ PK.pt q q∈ ∷ PK.pt p p∈ ∷ ι m ∷ [])
             ⊨ᵐ (var f1 ≐ con m_b) ⟩
    pin₁ = sym q_b
    pin₂ : ⟨ (ι m ∷ PK.pt q q∈ ∷ PK.pt p p∈ ∷ ι m ∷ [])
             ⊨ᵐ (var f2 ≐ con mₐ) ⟩
    pin₂ = sym qₐ
    ms : ⟨ (ι m ∷ PK.pt q q∈ ∷ PK.pt p p∈ ∷ ι m ∷ [])
           ⊨ᵐ ((var f0 ≐ var f2) ∨̇ (var f0 ≐ var f1)) ⟩
    ms = F0-spec p q (⟪ C ⟫↪ m) .fst h

  -- The pairing equation, closed: every member of a pair is one of the two
  -- arguments, so the caller supplies no subset certificate.
  wsub : (x : S) → ⟨ x ∈ˢ F0 p q ⟩ → ⟨ x ∈ˢ C ⟩
  wsub x h = PT.rec (snd (x ∈ˢ C)) go (F0-spec p q x .fst h)
    where
    go : (x ≡ p) ⊎ (x ≡ q) → ⟨ x ∈ˢ C ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) p∈
    go (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) q∈

  F0-defSet≡ : defSet pinned ≡ F0 p q
  F0-defSet≡ = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ defSet pinned ⟩ → ⟨ x ∈ˢ F0 p q ⟩
    sub x h = subst (λ w → ⟨ w ∈ˢ F0 p q ⟩) (fib .snd) (pinned-out (fib .fst) sat)
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = DefC.defSet⊆A pinned x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
      sat : ⟨ (ι (fib .fst) ∷ []) ⊨ᵐ pinned ⟩
      sat = subst ⟨_⟩ (DefC.defSet-mem pinned (fib .fst))
        (subst (λ w → ⟨ w ∈ˢ defSet pinned ⟩) (sym (fib .snd)) h)
    sup : (x : S) → ⟨ x ∈ˢ F0 p q ⟩ → ⟨ x ∈ˢ defSet pinned ⟩
    sup x h = subst (λ w → ⟨ w ∈ˢ defSet pinned ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (DefC.defSet-mem pinned (fib .fst)))
        (pinned-in (fib .fst)
          (subst (λ w → ⟨ w ∈ˢ F0 p q ⟩) (sym (fib .snd)) h)))
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = wsub x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
```

<!--en-->
## Pairing, and the sixteen values, in the stage

The stage facts assemble here. `Lpair`{.Agda} lands the unordered pair one
stage above the stage that holds both arguments. `ValuesInU`{.Agda} states
the sixteen values' landing: a value of any of the sixteen operations at
arguments drawn from `u` or from `u` itself is a member of the stage at the
offset. The four-step alias `suc⁴`{.Agda} is the reduction's index offset,
sealed so the successor layers stay out of conversion position.
<!--zh-->
## 配对与十六个值，落进阶段

阶段事实在此装配。`Lpair`{.Agda} 把无序对放到收下两个实参的阶段之上一个阶段。`ValuesInU`{.Agda} 陈述十六个值的落地：十六运算中任一运算在取自 `u` 或 `u` 自身的实参处的值，是偏移处那个阶段的成员。四步别名 `suc⁴`{.Agda} 是归约的索引偏移，被封起，使后继层远离转换位置。
<!--/-->

```agda
Lpair : (ζ p q : S) → ⟨ p ∈ˢ Lset ζ ⟩ → ⟨ q ∈ˢ Lset ζ ⟩
      → ⟨ F0 p q ∈ˢ Lset (sucV ζ) ⟩
Lpair ζ p q p∈ q∈ = 𝒟ₒ⊆Lsuc ζ (F0 p q)
  (𝒟ₒ-intro (Lset ζ) (F0 p q) ∣ FA.pinned , FA.F0-defSet≡ ∣₁)
  where
  module FA = F0Arm (Lset ζ) (Ltr ζ) p q p∈ q∈

ValuesInU : (u ζ : S) → Type (ℓ-suc ℓ)
ValuesInU u ζ = (i : Op16) (a b : S)
  → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u))
  → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩

opaque
  -- perf: P-i layer cap: four exposed Lset ∘ sucV layers doubled the check;
  -- the alias keeps at most one layer in conversion position.
  suc⁴ : S → S
  suc⁴ ζ = sucV (sucV (sucV (sucV ζ)))
```
