# The switch theorem

<!--en-->
This is the chapter that carries the two pieces the switch theorem's bridge
consumes: the reverse hops and the description side. The reverse hops close
the five cells the description chapter left walled, repacking each
description's own shape into a write lemma's flat decomposition and landing
in the image. The description side is the two-directional step: a set below
`u` whose membership is characterized by a Δ₀ formula is exactly that
formula's definable subset.
<!--zh-->
本章所携带的，正是切换定理的桥所取用的两件：反向跳与描述一侧。反向跳封住描述章留下的五格受阻，把每条描述自家的形状重新打包为写引理的扁平拆解，落进像中。描述一侧是那个双向的一步：`u` 之下的一个集合，若其隶属被一条 Δ₀ 公式刻画，则它恰是该公式的可定义子集。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.Switch {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import Base.Classical using ( lowerLEM )
open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write; F3; F3-write
        ; F4; F4-write; F5; F5-spec
        ; F6; F6-write; F7; F7-read; F7-write )
open import L.Rud.Describe {ℓ}
  using ( module Chain; module F2Desc; module F3Desc; module F4Desc
        ; module F6Desc; module F7Desc )
import FOL.Semantics
open import L.Rud.Images {ℓ} using ( F10; F10-spec )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; ⊤̇ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-⊤ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Step {ℓ} lem A
  using ( singl≡pair; Op16; Fof; step; step-out; StepArm; arm-member; arm-self
        ; arm-image )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _⊆_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber
        ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Two memberships and one classical spend

The tree carries the same membership relation at two levels: the structure's
`∈ˢ`, which every operation specification speaks, and the library's small `∈ₛ`,
which the description side's two-directional lemma speaks. The two bridges
below are stated with every set explicit, so no implicit is ever inverted
through a truth-value projection (lesson I-4). The classical law is lowered
once and spent through double negation, exactly where the D-7 ruling put it:
at the intersection.
<!--zh-->
## 两种隶属与一笔经典支出

树在两个层级上携带同一个隶属关系：结构的 `∈ˢ`，每条运算规格所说的；以及库的小 `∈ₛ`，描述一侧的双向引理所说的。下面两座桥把每个集合都写明，于是没有任何隐参需要经真值投影反解 (法则 I-4)。经典律降层一次，经双重否定花出，恰在 D-7 裁定所安放之处：交。
<!--/-->

```agda
∈s : (a b : V ℓ) → ⟨ a ∈ˢ b ⟩ → ⟨ a ∈ₛ b ⟩
∈s a b = ∈∈ₛ {a = a} {b = b} .fst

∈S : (a b : V ℓ) → ⟨ a ∈ₛ b ⟩ → ⟨ a ∈ˢ b ⟩
∈S a b = ∈∈ₛ {a = a} {b = b} .snd

opaque
  lemL : LEM ℓ
  lemL = lowerLEM lem

dne : (P : hProp ℓ) → ((⟨ P ⟩ → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
dne P nn = Sum.rec (λ p → p) (λ np → Empty.rec (nn np)) (lemL P)
```

<!--en-->
## The transparent operations

Pairing and difference are the basis functions themselves, and their
specifications are the operations chapter's, read across the membership
bridge. The union is the same basis function on its diagonal.
<!--zh-->
## 透明运算

配对与差就是基函数本身，其规格即运算章的规格，经隶属之桥读出。并是同一个基函数在对角上的施用。
<!--/-->

```agda
pairSpec : (a b y : V ℓ)
  → (⟨ y ∈ₛ F0 a b ⟩ → ⟨ (y ≡ₕ a) ⊔ (y ≡ₕ b) ⟩)
  × (⟨ (y ≡ₕ a) ⊔ (y ≡ₕ b) ⟩ → ⟨ y ∈ₛ F0 a b ⟩)
pairSpec a b y = (λ h → F0-spec a b y .fst (∈S y (F0 a b) h))
               , (λ s → ∈s y (F0 a b) (F0-spec a b y .snd s))

diffSpec : (a b y : V ℓ)
  → (⟨ y ∈ₛ F1 a b ⟩ → ⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥))
  × ((⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥)) → ⟨ y ∈ₛ F1 a b ⟩)
diffSpec a b y = fwd , bwd
  where
  fwd : ⟨ y ∈ₛ F1 a b ⟩ → ⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥)
  fwd h = ∈s y a (F1-spec a b y .fst (∈S y (F1 a b) h) .fst)
        , λ k → F1-spec a b y .fst (∈S y (F1 a b) h) .snd (∈S y b k)
  bwd : (⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥)) → ⟨ y ∈ₛ F1 a b ⟩
  bwd (y∈a , y∉b) = ∈s y (F1 a b)
    (F1-spec a b y .snd (∈S y a y∈a , λ k → y∉b (∈s y b k)))

opaque
  unionOp : V ℓ → V ℓ
  unionOp a = F5 a a

```

<!--en-->
## The intersection, and the classical spend

The orthodox sixteen-function list has no intersection, so the D-7 ruling
stands: intersection is the double difference, and its forward direction is the
one place excluded middle is spent.
<!--zh-->
## 交，及那笔经典支出

正统的十六函数表没有交，故 D-7 裁定成立：交是二重差，其正向是花掉排中律的唯一一处。
<!--/-->

```agda
opaque
  interOp : V ℓ → V ℓ → V ℓ
  interOp a b = F1 a (F1 a b)

  interSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ interOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩) → ⟨ y ∈ₛ interOp a b ⟩)
  interSpec a b y = fwd , bwd
    where
    fwd : ⟨ y ∈ₛ interOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩
    fwd h = y∈a , dne (y ∈ₛ b) (λ y∉b → parts .snd (diffSpec a b y .snd (y∈a , y∉b)))
      where
      parts : ⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ F1 a b ⟩ → Empty.⊥)
      parts = diffSpec a (F1 a b) y .fst h
      y∈a : ⟨ y ∈ₛ a ⟩
      y∈a = parts .fst
    bwd : (⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩) → ⟨ y ∈ₛ interOp a b ⟩
    bwd (y∈a , y∈b) = diffSpec a (F1 a b) y .snd
      (y∈a , λ k → diffSpec a b y .fst k .snd y∈b)

```

<!--en-->
## The two spellings of the pair

The pairing function and the coding chapter's `pr` denote the same operation;
the equation below reconciles their two spellings, and it is the singleton
law.
<!--zh-->
## 对的两种拼法

配对函数与编码章的 `pr` 指同一个运算；下面的方程调和它们的两种拼法，那就是单点集律。
<!--/-->

```agda
prAsF0 : (x z : V ℓ) → F0 (F0 x x) (F0 x z) ≡ pr x z
prAsF0 x z = cong (λ w → ⁅ w , ⁅ x , z ⁆ ⁆) (sym (singl≡pair x))

opaque
  memOp : V ℓ → V ℓ
  memOp a = F7 a a

```

<!--en-->
## Collection

The collection operation cuts `b` down to the members that contain
`a`. It is a slice of the membership relation: take the relation restricted to
`{a} ∪ b`, cut it to the pairs whose left coordinate is `a` and whose right
coordinate lies in `b`, and read the slice at `a` with the one image operation
whose argument is a single point.
<!--zh-->
## 收集

收集运算把 `b` 削减为含有 `a` 的那些成员。它是隶属关系的一个切片：取限制在 `{a} ∪ b` 上的关系，切到左坐标为 `a`、右坐标落在 `b` 中的那些对，再用单点参数的那个像运算读出 `a` 处的切片。
<!--/-->

```agda
opaque
  sUnion : V ℓ → V ℓ → V ℓ
  sUnion a b = F5 (F0 (F0 a a) b) (F0 (F0 a a) b)

  a∈sUnion : (a b : V ℓ) → ⟨ a ∈ˢ sUnion a b ⟩
  a∈sUnion a b = F5-spec (F0 (F0 a a) b) (F0 (F0 a a) b) a .snd
    ∣ F0 a a , ( F0-spec (F0 a a) b (F0 a a) .snd ∣ inl refl ∣₁
               , F0-spec a a a .snd ∣ inl refl ∣₁ ) ∣₁

  mem∈sUnion : (a b y : V ℓ) → ⟨ y ∈ˢ b ⟩ → ⟨ y ∈ˢ sUnion a b ⟩
  mem∈sUnion a b y y∈b = F5-spec (F0 (F0 a a) b) (F0 (F0 a a) b) y .snd
    ∣ b , ( F0-spec (F0 a a) b b .snd ∣ inr refl ∣₁ , y∈b ) ∣₁

  colGraph : V ℓ → V ℓ → V ℓ
  colGraph a b = interOp (F7 (sUnion a b) (sUnion a b)) (F2 (F0 a a) b)

  colOp : V ℓ → V ℓ → V ℓ
  colOp a b = F10 (colGraph a b) a

  colSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ colOp a b ⟩ → ⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩)
    × ((⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩) → ⟨ y ∈ₛ colOp a b ⟩)
  colSpec a b y = fwd , bwd
    where
    s : V ℓ
    s = sUnion a b
    fwd : ⟨ y ∈ₛ colOp a b ⟩ → ⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩
    fwd h = y∈b , a∈y
      where
      inGraph : ⟨ pr a y ∈ₛ colGraph a b ⟩
      inGraph = ∈s (pr a y) (colGraph a b)
        (subst ⟨_⟩ (F10-spec (colGraph a b) a y) (∈S y (colOp a b) h))
      parts : ⟨ pr a y ∈ₛ F7 s s ⟩ × ⟨ pr a y ∈ₛ F2 (F0 a a) b ⟩
      parts = interSpec (F7 s s) (F2 (F0 a a) b) (pr a y) .fst inGraph
      y∈b : ⟨ y ∈ₛ b ⟩
      y∈b = PT.rec (snd (y ∈ₛ b))
        (λ { (p , q , p∈ , q∈b , e) →
           ∈s y b (subst (λ w → ⟨ w ∈ˢ b ⟩)
             (sym (pr-inj {a = a} {b = y} {c = p} {d = q} e .snd)) q∈b) })
        (F2-read (F0 a a) b (pr a y) (∈S (pr a y) (F2 (F0 a a) b) (parts .snd)))
      a∈y : ⟨ a ∈ₛ y ⟩
      a∈y = PT.rec (snd (a ∈ₛ y))
        (λ { (p , q , p∈s , q∈s , p∈q , e) →
           ∈s a y (subst (λ w → ⟨ a ∈ˢ w ⟩)
             (sym (pr-inj {a = a} {b = y} {c = p} {d = q} e .snd))
             (subst (λ w → ⟨ w ∈ˢ q ⟩)
               (sym (pr-inj {a = a} {b = y} {c = p} {d = q} e .fst)) p∈q)) })
        (F7-read s s (pr a y) (∈S (pr a y) (F7 s s) (parts .fst)))
    bwd : (⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩) → ⟨ y ∈ₛ colOp a b ⟩
    bwd (y∈b , a∈y) = ∈s y (colOp a b)
      (subst ⟨_⟩ (sym (F10-spec (colGraph a b) a y))
        (∈S (pr a y) (colGraph a b) inGraph))
      where
      in7 : ⟨ pr a y ∈ˢ F7 s s ⟩
      in7 = F7-write s s (pr a y)
        ∣ a , y , ( a∈sUnion a b , mem∈sUnion a b y (∈S y b y∈b)
                  , ∈S a y a∈y , refl ) ∣₁
      in2 : ⟨ pr a y ∈ˢ F2 (F0 a a) b ⟩
      in2 = F2-write (F0 a a) b (pr a y)
        ∣ a , y , ( F0-spec a a a .snd ∣ inl refl ∣₁ , ∈S y b y∈b , refl ) ∣₁
      inGraph : ⟨ pr a y ∈ₛ colGraph a b ⟩
      inGraph = interSpec (F7 s s) (F2 (F0 a a) b) (pr a y) .snd
        ( ∈s (pr a y) (F7 s s) in7 , ∈s (pr a y) (F2 (F0 a a) b) in2 )

```

<!--en-->
## The conditional set

The conditional set is the domain of `c × t`, which is `c` exactly when `t`
has a member.
<!--zh-->
## 条件集

条件集是 `c × t` 的定义域，恰当 `t` 有成员时它就是 `c`。
<!--/-->

```agda
opaque
  condOp : V ℓ → V ℓ → V ℓ
  condOp t c = F6 (F2 c t) (F2 c t)

```

<!--en-->
## The reverse hops

The description chapter recorded five cells as walled: for the five sealed
operations the direction from the classical shape back into the image could
not be built, because the specification's right-hand side sits inside the
seal and the read lemmas travel one way. The write lemmas the operations
chapter now carries are exactly the missing direction, and the five closures
below are their consumers: each takes the description's own shape, repacks it
into the write's flat decomposition, and lands in the image. With them each
of the five descriptions is adequate in both directions.
<!--zh-->
## 反向跳

描述章记录了五格受阻：对五个封存运算，从经典形状回到像的方向造不出来，因为规格的右端坐在封印之内，而读引理只走一个方向。运算章如今携带的写引理恰是那个缺失的方向，下面五条封口就是它们的消费者：各自取描述自家的形状，重新打包为写引理的扁平拆解，落进像中。有了它们，五条描述在两个方向上都适足。
<!--/-->

```agda
module Hops (C a b : V ℓ) (a∈ : ⟨ a ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
  (Ctrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ C)) where
  module SemC = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemC.At (⟪ C ⟫) (⟪ C ⟫↪) using ( _⊨_ )
  module D2 = F2Desc C a b a∈ b∈
  module D3 = F3Desc C a b a∈ b∈
  module D4 = F4Desc C a b a∈ b∈
  module D6 = F6Desc C a b a∈ Ctrans
  module D7 = F7Desc C a b a∈

  F2-DRHS-mem : (v : V ℓ) → ⟨ D2.F2-DRHS a b v ⟩ → ⟨ v ∈ˢ F2 a b ⟩
  F2-DRHS-mem v h = F2-write a b v (PT.rec squash₁ outer h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ] (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p q ⟩)
    outer : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ w →
              (u ∈ˢ a) ⊓ ((w ∈ˢ b) ⊓ (v ≡ₕ pr u w))) ⟩ → ∥ D ∥₁
    outer (u , hu) = PT.rec squash₁
      (λ { (w , u∈a , w∈b , v≡) → ∣ u , w , (u∈a , w∈b , v≡) ∣₁ }) hu

  F2-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ D2.Φ₂ ⟩ → ⟨ v ∈ˢ F2 a b ⟩
  F2-desc-out v h = F2-DRHS-mem v (D2.F2-sat-out v h)

  F3-DRHS-mem : (v : V ℓ) → ⟨ D3.F3-DRHS a b v ⟩ → ⟨ v ∈ˢ F3 a b ⟩
  F3-DRHS-mem v h = F3-write a b v (PT.rec squash₁ outer h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ w ∈ V ℓ ]
          (⟨ z ∈ˢ a ⟩ × ⟨ pr u w ∈ˢ b ⟩ × ⟨ v ≡ₕ pr u (pr z w) ⟩)
    outer : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ z → ⋁ (V ℓ) (λ w →
              (z ∈ˢ a) ⊓ ((pr u w ∈ˢ b) ⊓ (v ≡ₕ pr u (pr z w))))) ⟩ → ∥ D ∥₁
    outer (u , hu) = PT.rec squash₁ mid hu
      where
      mid : Σ[ z ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ w →
              (z ∈ˢ a) ⊓ ((pr u w ∈ˢ b) ⊓ (v ≡ₕ pr u (pr z w)))) ⟩ → ∥ D ∥₁
      mid (z , hz) = PT.rec squash₁
        (λ { (w , z∈a , pr∈b , v≡) → ∣ u , z , w , (z∈a , pr∈b , v≡) ∣₁ }) hz

  F3-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ D3.Φ₃ ⟩ → ⟨ v ∈ˢ F3 a b ⟩
  F3-desc-out v h = F3-DRHS-mem v (D3.F3-sat-out v h)

  F4-DRHS-mem : (v : V ℓ) → ⟨ D4.F4-DRHS a b v ⟩ → ⟨ v ∈ˢ F4 a b ⟩
  F4-DRHS-mem v h = F4-write a b v (PT.rec squash₁ outer h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ] Σ[ z ∈ V ℓ ]
          (⟨ z ∈ˢ a ⟩ × ⟨ pr u w ∈ˢ b ⟩ × ⟨ v ≡ₕ pr u (pr w z) ⟩)
    outer : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ z → ⋁ (V ℓ) (λ w →
              (z ∈ˢ a) ⊓ ((pr u w ∈ˢ b) ⊓ (v ≡ₕ pr u (pr w z))))) ⟩ → ∥ D ∥₁
    outer (u , hu) = PT.rec squash₁ mid hu
      where
      mid : Σ[ z ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ w →
              (z ∈ˢ a) ⊓ ((pr u w ∈ˢ b) ⊓ (v ≡ₕ pr u (pr w z)))) ⟩ → ∥ D ∥₁
      mid (z , hz) = PT.rec squash₁
        (λ { (w , z∈a , pr∈b , v≡) → ∣ u , w , z , (z∈a , pr∈b , v≡) ∣₁ }) hz

  F4-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ D4.Φ₄ ⟩ → ⟨ v ∈ˢ F4 a b ⟩
  F4-desc-out v h = F4-DRHS-mem v (D4.F4-sat-out v h)

  F6-DRHS-mem : (v : V ℓ) → ⟨ D6.F6-DRHS a v ⟩ → ⟨ v ∈ˢ F6 a b ⟩
  F6-DRHS-mem v h = F6-write a b v (PT.rec squash₁ outer h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ] (⟨ pr u w ∈ˢ a ⟩ × ⟨ v ≡ₕ u ⟩)
    outer : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ w → (pr u w ∈ˢ a) ⊓ (v ≡ₕ u)) ⟩ → ∥ D ∥₁
    outer (u , hu) = PT.rec squash₁
      (λ { (w , pr∈a , v≡) → ∣ u , w , (pr∈a , v≡) ∣₁ }) hu

  F6-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ D6.Φ₆ ⟩ → ⟨ v ∈ˢ F6 a b ⟩
  F6-desc-out v h = F6-DRHS-mem v (D6.F6-sat-out v h)

  F7-DRHS-mem : (v : V ℓ) → ⟨ D7.F7-DRHS a v ⟩ → ⟨ v ∈ˢ F7 a b ⟩
  F7-DRHS-mem v h = F7-write a b v (PT.rec squash₁ outer h)
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ]
          (⟨ u ∈ˢ a ⟩ × ⟨ w ∈ˢ a ⟩ × ⟨ u ∈ˢ w ⟩ × ⟨ v ≡ₕ pr u w ⟩)
    outer : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ w →
              (u ∈ˢ a) ⊓ ((w ∈ˢ a) ⊓ ((u ∈ˢ w) ⊓ (v ≡ₕ pr u w)))) ⟩ → ∥ D ∥₁
    outer (u , hu) = PT.rec squash₁
      (λ { (w , u∈a , w∈a , u∈w , v≡) → ∣ u , w , (u∈a , w∈a , u∈w , v≡) ∣₁ }) hu

  F7-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ D7.Φ₇ ⟩ → ⟨ v ∈ˢ F7 a b ⟩
  F7-desc-out v h = F7-DRHS-mem v (D7.F7-sat-out v h)
```

<!--en-->
## The description side

A member of the one-step closure that happens to be a subset of `u` is
definable over `u`: it is the extension of a formula. The generic step is one
lemma, the two-directional description: a set below `u` whose membership is
characterized by a Δ₀ formula is that formula's definable subset, on the nose.
The step's own three arms are then read off. The member arm and the self arm
are immediate, with the membership atom and the true formula; the image arm is
the sixteen descriptions, and is where this chapter stops.
<!--zh-->
## 描述一侧

一步闭包的成员，若恰好是 `u` 的子集，则在 `u` 上可定义：它是某条公式的外延。通用的一步是一条引理，即双向描述：`u` 之下的一个集合，若其隶属被一条 Δ₀ 公式刻画，则它恰是该公式的可定义子集。step 自身的三条臂随之读出。成员臂与自身臂立刻就有，用隶属原子与真公式；像臂是十六条描述，本章在那里止步。
<!--/-->

```agda
module Descr (u : V ℓ) (utrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ u)) where
  module Chu = Chain u utrans
  module Defu = DefOf u
  module SemU = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemU.At (⟪ u ⟫) (⟪ u ⟫↪) using ( _⊨_ )

  described : (x : V ℓ) (Φ : Formula ⟪ u ⟫ 1) → Δ₀ Φ
            → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ u ⟩)
            → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩)
            → ((v : V ℓ) → ⟨ v ∈ˢ u ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ x ⟩)
            → Defu.defSet Φ ≡ x
  described x Φ dΦ sub din dout =
    extensionality (Defu.defSet Φ) x (sub₁ , sub₂)
    where
    sub₁ : ⟨ Defu.defSet Φ ⊆ x ⟩
    sub₁ y y∈ = ∈s y x (subst (λ w → ⟨ w ∈ˢ x ⟩) (fib .snd)
      (dout (⟪ u ⟫↪ (fib .fst)) (∈S (⟪ u ⟫↪ (fib .fst)) u (∈ₛ⟪ u ⟫↪ (fib .fst)))
        (subst ⟨_⟩ (Chu.chain Φ dΦ (fib .fst))
          (subst (λ w → ⟨ w ∈ˢ Defu.defSet Φ ⟩) (sym (fib .snd))
            (∈S y (Defu.defSet Φ) y∈)))))
      where
      y∈u : ⟨ y ∈ˢ u ⟩
      y∈u = Defu.defSet⊆A Φ y (∈S y (Defu.defSet Φ) y∈)
      fib : Σ[ m ∈ ⟪ u ⟫ ] (⟪ u ⟫↪ m ≡ y)
      fib = ∈-asFiber {a = y} {b = u} y∈u
    sub₂ : ⟨ x ⊆ Defu.defSet Φ ⟩
    sub₂ y y∈ = ∈s y (Defu.defSet Φ)
      (subst (λ w → ⟨ w ∈ˢ Defu.defSet Φ ⟩) (fib .snd)
        (subst ⟨_⟩ (sym (Chu.chain Φ dΦ (fib .fst)))
          (subst (λ w → ⟨ (w ∷ []) ⊨ Φ ⟩) (sym (fib .snd))
            (din y (∈S y x y∈)))))
      where
      y∈u : ⟨ y ∈ˢ u ⟩
      y∈u = sub y (∈S y x y∈)
      fib : Σ[ m ∈ ⟪ u ⟫ ] (⟪ u ⟫↪ m ≡ y)
      fib = ∈-asFiber {a = y} {b = u} y∈u

  memArm : (x : V ℓ) → ⟨ x ∈ˢ u ⟩
         → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ u ⟩)
         → Σ[ Φ ∈ Formula ⟪ u ⟫ 1 ] (Defu.defSet Φ ≡ x)
  memArm x x∈u sub = Φ , described x Φ δ-∈ sub din dout
    where
    fib : Σ[ m ∈ ⟪ u ⟫ ] (⟪ u ⟫↪ m ≡ x)
    fib = ∈-asFiber {a = x} {b = u} x∈u
    Φ : Formula ⟪ u ⟫ 1
    Φ = var zero ∈̇ con (fib .fst)
    din : (v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
    din v h = subst (λ w → ⟨ v ∈ˢ w ⟩) (sym (fib .snd)) h
    dout : (v : V ℓ) → ⟨ v ∈ˢ u ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ x ⟩
    dout v _ h = subst (λ w → ⟨ v ∈ˢ w ⟩) (fib .snd) h

  selfArm : Σ[ Φ ∈ Formula ⟪ u ⟫ 1 ] (Defu.defSet Φ ≡ u)
  selfArm = ⊤̇ , described u ⊤̇ δ-⊤ (λ v h → h) (λ v h → tt*) (λ v h _ → h)

  ImgArm : Type (ℓ-suc ℓ)
  ImgArm = (i : Op16) (a b : V ℓ)
         → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u))
         → ((v : V ℓ) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ u ⟩)
         → Σ[ Φ ∈ Formula ⟪ u ⟫ 1 ] (Defu.defSet Φ ≡ Fof i a b)

  switch-⊆ : ImgArm → (x : V ℓ) → ⟨ x ∈ˢ step u ⟩
           → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ u ⟩)
           → ⟨ x ∈ˢ Defu.Def ⟩
  switch-⊆ imgArm x x∈step sub =
    PT.rec (snd (x ∈ˢ Defu.Def)) go (step-out u x x∈step)
    where
    go : StepArm u x → ⟨ x ∈ˢ Defu.Def ⟩
    go (arm-member x∈u) = ∣ memArm x x∈u sub .fst , memArm x x∈u sub .snd ∣₁
    go (arm-self x≡u) = ∣ selfArm .fst , selfArm .snd ∙ sym x≡u ∣₁
    go (arm-image i a b sa sb x≡) =
      ∣ r .fst , r .snd ∙ sym x≡ ∣₁
      where
      subF : (v : V ℓ) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ u ⟩
      subF v h = sub v (subst (λ w → ⟨ v ∈ˢ w ⟩) (sym x≡) h)
      r : Σ[ Φ ∈ Formula ⟪ u ⟫ 1 ] (Defu.defSet Φ ≡ Fof i a b)
      r = imgArm i a b sa sb subF
```

<!--en-->
## Recap

The chapter is exactly the two pieces its consumer, the bridge, takes: the
reverse hops and the description side. The reverse hops close the five cells
the description chapter left walled, each one repacking the description's own
shape into a write lemma's flat decomposition and landing in the image, so the
five descriptions are adequate in both directions. The description side is the
two-directional step: a set below `u` whose membership is characterized by a
Δ₀ formula is exactly that formula's definable subset. The member arm and the
self arm are discharged here, and the image arm stands as the chapter's one
residue: the sixteen descriptions instantiated at a level, including the case
where an argument is the level itself, which the descriptions as delivered do
not cover.
<!--zh-->
## 小结

本章恰是其消费者即桥所读的两件：反向跳与描述一侧。反向跳封住描述章留下的五格受阻，每条都把描述自家的形状重新打包为写引理的扁平拆解并落进像中，于是五条描述在两个方向上都适足。描述一侧是双向的一步：`u` 之下的一个集合，若其隶属被一条 Δ₀ 公式刻画，则它恰是该公式的可定义子集。成员臂与自身臂在此清偿，像臂作为本章唯一存留而立：十六条描述在某一层处的实例，包括实参就是该层自身的情形，而现交付的诸描述并不覆盖它。
<!--/-->
