# The switch theorem

<!--en-->
This is the chapter where the two faces meet. The realization half proved that
every Δ₀-definable subset of a transitive set is the value of a finite
composite of an abstract basis; the description half turned each of the sixteen
concrete operations back into a defining formula. Here the abstract basis is
discharged at the concrete operations, and the two halves are joined into the
comprehension statement: on subsets of a transitive `u`, membership in the rud
closure and definability over `u` are the same thing.
<!--zh-->
本章是两副面孔相遇之处。领悟半边证明了传递集的每个 Δ₀ 可定义子集都是某个抽象基的有限复合之值；描述半边把十六个具体运算各自译回一条定义公式。此处抽象基在具体运算处兑付，两半接合为领悟陈述：在传递集 `u` 的子集上，属于初步函数闭包与在 `u` 上可定义，是同一件事。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module L.Rud.Switch {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import Base.Classical using ( lowerLEM )
open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F2; F2-read; F2-write; F3; F3-write
        ; F4; F4-write; F5; F5-spec
        ; F6; F6-read; F6-write; F7; F7-read; F7-write; F9 )
open import L.Rud.Describe {ℓ}
  using ( module Chain; module F2Desc; module F3Desc; module F4Desc
        ; module F6Desc; module F7Desc )
import FOL.Semantics
open import L.Rud.Images {ℓ} using ( F10; F10-spec )
open import FOL.Syntax using
  ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Realize {ℓ} lem
  using ( _⊓ₚ_; _⊓₂_; ∃ₚ; ∃ₚ⁺; module Basis )
open import L.Rud.Step {ℓ} lem A
  using ( singl≡pair; Op16; f0; f1; f2; f5; f6; f7; f9; f10; Fof
        ; Fof-f0; Fof-f1; Fof-f2; Fof-f5; Fof-f6; Fof-f7; Fof-f9; Fof-f10
        ; step; step-out; StepArm; arm-member; arm-self; arm-image
        ; Jset; Jset-rud; Sset-trans; Sset-mem; Sset-mono )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Equiv using ( equivFun; invEquiv )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _∼_; _⊆_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber
        ; identityPrinciple; extensionality )
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
which the realization's telescope speaks. The two bridges below are stated with
every set explicit, so no implicit is ever inverted through a truth-value
projection (lesson I-4). The classical law is lowered once and spent through
double negation, exactly where the D-7 ruling put it: at the intersection.
<!--zh-->
## 两种隶属与一笔经典支出

树在两个层级上携带同一个隶属关系：结构的 `∈ˢ`，每条运算规格所说的；以及库的小 `∈ₛ`，领悟的参数表所说的。下面两座桥把每个集合都写明，于是没有任何隐参需要经真值投影反解 (法则 I-4)。经典律降层一次，经双重否定花出，恰在 D-7 裁定所安放之处：交。
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
## The four transparent operations

Pairing, difference, union and the product are the basis functions themselves.
Their specifications are the operations chapter's, read across the membership
bridge; only the product needs the reads, because its right-hand side sits
inside the seal.
<!--zh-->
## 四个透明运算

配对、差、并与积就是基函数本身。它们的规格即运算章的规格，经隶属之桥读出；唯有积需要读引理，因为其右端坐在封印之内。
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

  unionSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ unionOp a ⟩ → ⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩)
    × (⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩ → ⟨ y ∈ₛ unionOp a ⟩)
  unionSpec a y = fwd , bwd
    where
    T : hProp (ℓ-suc ℓ)
    T = ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z))
    fwd : ⟨ y ∈ₛ unionOp a ⟩ → ⟨ T ⟩
    fwd h = PT.rec (snd T)
      (λ { (z , z∈a , y∈z) → ∣ z , (∈s z a z∈a , ∈s y z y∈z) ∣₁ })
      (F5-spec a a y .fst (∈S y (unionOp a) h))
    bwd : ⟨ T ⟩ → ⟨ y ∈ₛ unionOp a ⟩
    bwd s = ∈s y (unionOp a) (F5-spec a a y .snd
      (PT.rec (snd (F5-RHS' a y))
        (λ { (z , z∈a , y∈z) → ∣ z , (∈S z a z∈a , ∈S y z y∈z) ∣₁ }) s))
      where
      F5-RHS' : (x t : V ℓ) → hProp (ℓ-suc ℓ)
      F5-RHS' x t = ⋁ (V ℓ) (λ v → (v ∈ˢ x) ⊓ (t ∈ˢ v))

```

<!--en-->
## The intersection, and the classical spend

The orthodox sixteen-function list has no intersection, so the D-7 ruling
stands: intersection is the double difference, and its forward direction is the
one place the realization's algebra spends excluded middle.
<!--zh-->
## 交，及那笔经典支出

正统的十六函数表没有交，故 D-7 裁定成立：交是二重差，其正向是领悟的代数花掉排中律的唯一一处。
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
## The pair, spelled with the pairing function

The realization's telescope states the product and the membership relation
with the Kuratowski pair written out of the pairing operation itself, so the
interface never mentions the coding chapter. One equation reconciles the two
spellings, and it is the singleton law.
<!--zh-->
## 用配对函数拼写的对

领悟的参数表把积与隶属关系里的 Kuratowski 对直接用配对运算拼出，故接口从不提及编码章。一条方程调和两种拼法，那就是单点集律。
<!--/-->

```agda
prAsF0 : (x z : V ℓ) → F0 (F0 x x) (F0 x z) ≡ pr x z
prAsF0 x z = cong (λ w → ⁅ w , ⁅ x , z ⁆ ⁆) (sym (singl≡pair x))

prodSpec : (a b y : V ℓ)
  → (⟨ y ∈ₛ F2 a b ⟩
     → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z →
         (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z))))) ⟩)
  × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z →
         (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z))))) ⟩
     → ⟨ y ∈ₛ F2 a b ⟩)
prodSpec a b y = fwd , bwd
  where
  T : hProp (ℓ-suc ℓ)
  T = ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z →
        (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z)))))
  fwd : ⟨ y ∈ₛ F2 a b ⟩ → ⟨ T ⟩
  fwd h = PT.rec (snd T)
    (λ { (p , q , p∈a , q∈b , y≡) →
       ∣ p , ∣ q , (∈s p a p∈a , ∈s q b q∈b
                   , subst (λ w → y ≡ w) (sym (prAsF0 p q)) y≡) ∣₁ ∣₁ })
    (F2-read a b y (∈S y (F2 a b) h))
  bwd : ⟨ T ⟩ → ⟨ y ∈ₛ F2 a b ⟩
  bwd s = ∈s y (F2 a b) (F2-write a b y (PT.rec squash₁ outer s))
    where
    D : Type (ℓ-suc ℓ)
    D = Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
          (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ y ≡ₕ pr p q ⟩)
    outer : Σ[ x ∈ V ℓ ] ⟨ ∃ₚ⁺ (λ z →
              (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z)))) ⟩
          → ∥ D ∥₁
    outer (x , hx) = PT.rec squash₁
      (λ { (z , x∈a , z∈b , y≡) →
         ∣ x , z , (∈S x a x∈a , ∈S z b z∈b
                   , subst (λ w → y ≡ w) (prAsF0 x z) y≡) ∣₁ }) hx

opaque
  memOp : V ℓ → V ℓ
  memOp a = F7 a a

  memSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ memOp a ⟩
       → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂
           ((x ∈ₛ z) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z)))))) ⟩)
    × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂
           ((x ∈ₛ z) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z)))))) ⟩
       → ⟨ y ∈ₛ memOp a ⟩)
  memSpec a y = fwd , bwd
    where
    T : hProp (ℓ-suc ℓ)
    T = ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂
          ((x ∈ₛ z) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z))))))
    fwd : ⟨ y ∈ₛ memOp a ⟩ → ⟨ T ⟩
    fwd h = PT.rec (snd T)
      (λ { (p , q , p∈a , q∈a , p∈q , y≡) →
         ∣ p , ∣ q , (∈s p a p∈a , ∈s q a q∈a , ∈s p q p∈q
                     , subst (λ w → y ≡ w) (sym (prAsF0 p q)) y≡) ∣₁ ∣₁ })
      (F7-read a a y (∈S y (memOp a) h))
    bwd : ⟨ T ⟩ → ⟨ y ∈ₛ memOp a ⟩
    bwd s = ∈s y (memOp a) (F7-write a a y (PT.rec squash₁ outer s))
      where
      D : Type (ℓ-suc ℓ)
      D = Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
            (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ y ≡ₕ pr p q ⟩)
      outer : Σ[ x ∈ V ℓ ] ⟨ ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂
                ((x ∈ₛ z) ⊓₂ (y ≡ₕ F0 (F0 x x) (F0 x z))))) ⟩
            → ∥ D ∥₁
      outer (x , hx) = PT.rec squash₁
        (λ { (z , x∈a , z∈a , x∈z , y≡) →
           ∣ x , z , (∈S x a x∈a , ∈S z a z∈a , ∈S x z x∈z
                     , subst (λ w → y ≡ w) (prAsF0 x z) y≡) ∣₁ }) hx

```

<!--en-->
## Collection

The telescope's collection operation cuts `b` down to the members that contain
`a`. It is a slice of the membership relation: take the relation restricted to
`{a} ∪ b`, cut it to the pairs whose left coordinate is `a` and whose right
coordinate lies in `b`, and read the slice at `a` with the one image operation
whose argument is a single point.
<!--zh-->
## 收集

参数表的收集运算把 `b` 削减为含有 `a` 的那些成员。它是隶属关系的一个切片：取限制在 `{a} ∪ b` 上的关系，切到左坐标为 `a`、右坐标落在 `b` 中的那些对，再用单点参数的那个像运算读出 `a` 处的切片。
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
## The conditional set, and the two separations

Characteristic separation and equality separation share one shape: keep `c` if
a test set is inhabited, and keep nothing otherwise. The conditional set is the
domain of `c × t`, which is `c` exactly when `t` has a member. The two tests are
the membership witness, a one-point slice of the membership relation cut to the
pair `<a,b>`, and the equality witness, the intersection of the two singletons.
<!--zh-->
## 条件集与两种分离

特征分离与等词分离共享一个形状：若检验集有居民则留住 `c`，否则什么都不留。条件集是 `c × t` 的定义域，恰当 `t` 有成员时它就是 `c`。两个检验分别是隶属见证，即隶属关系切到对 `<a,b>` 的单点切片，以及等词见证，即两个单点集之交。
<!--/-->

```agda
opaque
  condOp : V ℓ → V ℓ → V ℓ
  condOp t c = F6 (F2 c t) (F2 c t)

  condSpec : (t c y : V ℓ)
    → (⟨ y ∈ₛ condOp t c ⟩ → ⟨ (y ∈ₛ c) ⊓₂ ∃ₚ (λ z → z ∈ₛ t) ⟩)
    × (⟨ (y ∈ₛ c) ⊓₂ ∃ₚ (λ z → z ∈ₛ t) ⟩ → ⟨ y ∈ₛ condOp t c ⟩)
  condSpec t c y = fwd , bwd
    where
    G : hProp (ℓ-suc ℓ)
    G = (y ∈ₛ c) ⊓₂ ∃ₚ (λ z → z ∈ₛ t)
    fwd : ⟨ y ∈ₛ condOp t c ⟩ → ⟨ G ⟩
    fwd h = PT.rec (snd G) outer
      (F6-read (F2 c t) (F2 c t) y (∈S y (condOp t c) h))
      where
      outer : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
                (⟨ pr p q ∈ˢ F2 c t ⟩ × ⟨ y ≡ₕ p ⟩) → ⟨ G ⟩
      outer (p , q , pq∈ , y≡p) = PT.rec (snd G) inner
        (F2-read c t (pr p q) pq∈)
        where
        inner : Σ[ p' ∈ V ℓ ] Σ[ q' ∈ V ℓ ]
                  (⟨ p' ∈ˢ c ⟩ × ⟨ q' ∈ˢ t ⟩ × ⟨ pr p q ≡ₕ pr p' q' ⟩) → ⟨ G ⟩
        inner (p' , q' , p'∈c , q'∈t , e) =
            ∈s y c (subst (λ w → ⟨ w ∈ˢ c ⟩)
              (sym (y≡p ∙ pr-inj {a = p} {b = q} {c = p'} {d = q'} e .fst)) p'∈c)
          , ∣ q' , ∈s q' t q'∈t ∣₁
    bwd : ⟨ G ⟩ → ⟨ y ∈ₛ condOp t c ⟩
    bwd (y∈c , ht) = PT.rec (snd (y ∈ₛ condOp t c)) go ht
      where
      go : Σ[ z ∈ V ℓ ] ⟨ z ∈ₛ t ⟩ → ⟨ y ∈ₛ condOp t c ⟩
      go (z , z∈t) = ∈s y (condOp t c)
        (F6-write (F2 c t) (F2 c t) y ∣ y , z , (in2 , refl) ∣₁)
        where
        in2 : ⟨ pr y z ∈ˢ F2 c t ⟩
        in2 = F2-write c t (pr y z)
          ∣ y , z , (∈S y c y∈c , ∈S z t z∈t , refl) ∣₁


opaque
  memWit : V ℓ → V ℓ → V ℓ
  memWit a b = interOp (F7 (F0 a b) (F0 a b)) (F0 (F9 a b) (F9 a b))

  memWit-out : (a b : V ℓ) → ⟨ ∃ₚ (λ z → z ∈ₛ memWit a b) ⟩ → ⟨ a ∈ₛ b ⟩
  memWit-out a b = PT.rec (snd (a ∈ₛ b)) go
    where
    go : Σ[ z ∈ V ℓ ] ⟨ z ∈ₛ memWit a b ⟩ → ⟨ a ∈ₛ b ⟩
    go (z , z∈W) = PT.rec (snd (a ∈ₛ b)) atPr
      (F0-spec (F9 a b) (F9 a b) z .fst (∈S z (F0 (F9 a b) (F9 a b)) (parts .snd)))
      where
      parts : ⟨ z ∈ₛ F7 (F0 a b) (F0 a b) ⟩ × ⟨ z ∈ₛ F0 (F9 a b) (F9 a b) ⟩
      parts = interSpec (F7 (F0 a b) (F0 a b)) (F0 (F9 a b) (F9 a b)) z .fst z∈W
      atPr : (z ≡ F9 a b) ⊎ (z ≡ F9 a b) → ⟨ a ∈ₛ b ⟩
      atPr d = PT.rec (snd (a ∈ₛ b)) read
        (F7-read (F0 a b) (F0 a b) z (∈S z (F7 (F0 a b) (F0 a b)) (parts .fst)))
        where
        z≡ : z ≡ pr a b
        z≡ = Sum.rec (λ p → p) (λ p → p) d
        read : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
                 (⟨ p ∈ˢ F0 a b ⟩ × ⟨ q ∈ˢ F0 a b ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩)
             → ⟨ a ∈ₛ b ⟩
        read (p , q , _ , _ , p∈q , e) = ∈s a b
          (subst (λ w → ⟨ a ∈ˢ w ⟩)
            (sym (pr-inj {a = a} {b = b} {c = p} {d = q} (sym z≡ ∙ e) .snd))
            (subst (λ w → ⟨ w ∈ˢ q ⟩)
              (sym (pr-inj {a = a} {b = b} {c = p} {d = q} (sym z≡ ∙ e) .fst)) p∈q))

  memWit-in : (a b : V ℓ) → ⟨ a ∈ₛ b ⟩ → ⟨ ∃ₚ (λ z → z ∈ₛ memWit a b) ⟩
  memWit-in a b a∈b = ∣ pr a b , inW ∣₁
    where
    in7 : ⟨ pr a b ∈ˢ F7 (F0 a b) (F0 a b) ⟩
    in7 = F7-write (F0 a b) (F0 a b) (pr a b)
      ∣ a , b , ( F0-spec a b a .snd ∣ inl refl ∣₁
                , F0-spec a b b .snd ∣ inr refl ∣₁ , ∈S a b a∈b , refl ) ∣₁
    in0 : ⟨ pr a b ∈ˢ F0 (F9 a b) (F9 a b) ⟩
    in0 = F0-spec (F9 a b) (F9 a b) (pr a b) .snd ∣ inl refl ∣₁
    inW : ⟨ pr a b ∈ₛ memWit a b ⟩
    inW = interSpec (F7 (F0 a b) (F0 a b)) (F0 (F9 a b) (F9 a b)) (pr a b) .snd
      ( ∈s (pr a b) (F7 (F0 a b) (F0 a b)) in7
      , ∈s (pr a b) (F0 (F9 a b) (F9 a b)) in0 )


opaque
  eqWit : V ℓ → V ℓ → V ℓ
  eqWit a b = interOp (F0 a a) (F0 b b)

  eqWit-out : (a b : V ℓ) → ⟨ ∃ₚ (λ z → z ∈ₛ eqWit a b) ⟩ → ⟨ a ∼ b ⟩
  eqWit-out a b = PT.rec (snd (a ∼ b)) go
    where
    go : Σ[ z ∈ V ℓ ] ⟨ z ∈ₛ eqWit a b ⟩ → ⟨ a ∼ b ⟩
    go (z , z∈W) = PT.rec (snd (a ∼ b)) left
      (F0-spec a a z .fst (∈S z (F0 a a) (parts .fst)))
      where
      parts : ⟨ z ∈ₛ F0 a a ⟩ × ⟨ z ∈ₛ F0 b b ⟩
      parts = interSpec (F0 a a) (F0 b b) z .fst z∈W
      left : (z ≡ a) ⊎ (z ≡ a) → ⟨ a ∼ b ⟩
      left d = PT.rec (snd (a ∼ b)) right
        (F0-spec b b z .fst (∈S z (F0 b b) (parts .snd)))
        where
        z≡a : z ≡ a
        z≡a = Sum.rec (λ p → p) (λ p → p) d
        right : (z ≡ b) ⊎ (z ≡ b) → ⟨ a ∼ b ⟩
        right d' = equivFun (invEquiv (identityPrinciple {a = a} {b = b}))
          (sym z≡a ∙ Sum.rec (λ p → p) (λ p → p) d')

  eqWit-in : (a b : V ℓ) → ⟨ a ∼ b ⟩ → ⟨ ∃ₚ (λ z → z ∈ₛ eqWit a b) ⟩
  eqWit-in a b s = ∣ a , inW ∣₁
    where
    a≡b : a ≡ b
    a≡b = equivFun (identityPrinciple {a = a} {b = b}) s
    inW : ⟨ a ∈ₛ eqWit a b ⟩
    inW = interSpec (F0 a a) (F0 b b) a .snd
      ( ∈s a (F0 a a) (F0-spec a a a .snd ∣ inl refl ∣₁)
      , ∈s a (F0 b b) (F0-spec b b a .snd ∣ inl a≡b ∣₁) )


opaque
  chSepOp : V ℓ → V ℓ → V ℓ → V ℓ
  chSepOp a b c = condOp (memWit a b) c

  chSepSpec : (a b c y : V ℓ)
    → (⟨ y ∈ₛ chSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩) → ⟨ y ∈ₛ chSepOp a b c ⟩)
  chSepSpec a b c y = fwd , bwd
    where
    fwd : ⟨ y ∈ₛ chSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩
    fwd h = parts .fst , memWit-out a b (parts .snd)
      where
      parts : ⟨ y ∈ₛ c ⟩ × ⟨ ∃ₚ (λ z → z ∈ₛ memWit a b) ⟩
      parts = condSpec (memWit a b) c y .fst h
    bwd : (⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩) → ⟨ y ∈ₛ chSepOp a b c ⟩
    bwd (y∈c , a∈b) = condSpec (memWit a b) c y .snd (y∈c , memWit-in a b a∈b)


opaque
  eqSepOp : V ℓ → V ℓ → V ℓ → V ℓ
  eqSepOp a b c = condOp (eqWit a b) c

  eqSepSpec : (a b c y : V ℓ)
    → (⟨ y ∈ₛ eqSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩)
    × ((⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩) → ⟨ y ∈ₛ eqSepOp a b c ⟩)
  eqSepSpec a b c y = fwd , bwd
    where
    fwd : ⟨ y ∈ₛ eqSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩
    fwd h = parts .fst , eqWit-out a b (parts .snd)
      where
      parts : ⟨ y ∈ₛ c ⟩ × ⟨ ∃ₚ (λ z → z ∈ₛ eqWit a b) ⟩
      parts = condSpec (eqWit a b) c y .fst h
    bwd : (⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩) → ⟨ y ∈ₛ eqSepOp a b c ⟩
    bwd (y∈c , a∼b) = condSpec (eqWit a b) c y .snd (y∈c , eqWit-in a b a∼b)

```

<!--en-->
## The image over a composite family

The image operation is the one slot of the telescope that no single basis
function fills: it must take a composite of one higher arity, a stack of
values for the ambient witness slots, and a set to range over, and return the
family's image. Because its value has to agree with the very evaluation it
sits inside, the evaluation is written here first, with the image inlined at
its own constructor, and the operation is then read off that clause. Nothing
is mutual, and the recursion is structural in the composite.
<!--zh-->
## 复合族上的像

像运算是参数表中没有任何单个基函数能填的那一格：它要取一个高一元数的复合、一摞环境见证槽的值、以及一个被遍历的集合，返回该族之像。由于其值必须与它所置身的那次求值一致，求值在此先行写出，像在其自身的构造子处内联，运算随后从该子句读出。没有相互递归，递归对复合是结构性的。
<!--/-->

```agda
module Bs = Basis F0 pairSpec F1 diffSpec interOp interSpec F2 prodSpec
                  memOp memSpec unionOp unionSpec colOp colSpec
                  chSepOp chSepSpec eqSepOp eqSepSpec

open Bs using ( Comp; conC; varC; interC; diffC; unionC; pairC; colC
              ; chSepC; eqSepC; imgC; Trans )

evalC : {k : ℕ} → Comp k → Vec (V ℓ) k → V ℓ
evalC (conC x) ws = x
evalC (varC i) ws = lookup i ws
evalC (interC a b) ws = interOp (evalC a ws) (evalC b ws)
evalC (diffC a b) ws = F1 (evalC a ws) (evalC b ws)
evalC (unionC a) ws = unionOp (evalC a ws)
evalC (pairC a b) ws = F0 (evalC a ws) (evalC b ws)
evalC (colC a b) ws = colOp (evalC a ws) (evalC b ws)
evalC (chSepC a b c) ws = chSepOp (evalC a ws) (evalC b ws) (evalC c ws)
evalC (eqSepC a b c) ws = eqSepOp (evalC a ws) (evalC b ws) (evalC c ws)
evalC (imgC f a) ws =
  sett ⟪ evalC a ws ⟫ (λ m → evalC f (⟪ evalC a ws ⟫↪ m ∷ ws))

imgOpC : {k : ℕ} → Comp (suc k) → Vec (V ℓ) k → V ℓ → V ℓ
imgOpC f vs p = sett ⟪ p ⟫ (λ m → evalC f (⟪ p ⟫↪ m ∷ vs))

module Ev = Bs.Eval imgOpC

eval-agree : {k : ℕ} (c : Comp k) (ws : Vec (V ℓ) k) → Ev.eval c ws ≡ evalC c ws
eval-agree (conC x) ws = refl
eval-agree (varC i) ws = refl
eval-agree (interC a b) ws i = interOp (eval-agree a ws i) (eval-agree b ws i)
eval-agree (diffC a b) ws i = F1 (eval-agree a ws i) (eval-agree b ws i)
eval-agree (unionC a) ws i = unionOp (eval-agree a ws i)
eval-agree (pairC a b) ws i = F0 (eval-agree a ws i) (eval-agree b ws i)
eval-agree (colC a b) ws i = colOp (eval-agree a ws i) (eval-agree b ws i)
eval-agree (chSepC a b c) ws i =
  chSepOp (eval-agree a ws i) (eval-agree b ws i) (eval-agree c ws i)
eval-agree (eqSepC a b c) ws i =
  eqSepOp (eval-agree a ws i) (eval-agree b ws i) (eval-agree c ws i)
eval-agree (imgC f a) ws i = imgOpC f ws (eval-agree a ws i)

imgSpecC : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p z : V ℓ)
  → (⟨ z ∈ₛ imgOpC f vs p ⟩
     → ⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ Ev.eval f (y ∷ vs))) ⟩)
  × (⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ Ev.eval f (y ∷ vs))) ⟩
     → ⟨ z ∈ₛ imgOpC f vs p ⟩)
imgSpecC {k} f vs p z = fwd , bwd
  where
  T : hProp (ℓ-suc ℓ)
  T = ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ Ev.eval f (y ∷ vs)))
  D : Type (ℓ-suc ℓ)
  D = Σ[ m ∈ ⟪ p ⟫ ] (evalC f (⟪ p ⟫↪ m ∷ vs) ≡ z)
  fwd : ⟨ z ∈ₛ imgOpC f vs p ⟩ → ⟨ T ⟩
  fwd h = PT.rec (snd T) go (∈S z (imgOpC f vs p) h)
    where
    go : D → ⟨ T ⟩
    go (m , q) = ∣ ⟪ p ⟫↪ m
      , ( ∈ₛ⟪ p ⟫↪ m
        , sym q ∙ sym (eval-agree f (⟪ p ⟫↪ m ∷ vs)) ) ∣₁
  bwd : ⟨ T ⟩ → ⟨ z ∈ₛ imgOpC f vs p ⟩
  bwd s = ∈s z (imgOpC f vs p) (PT.rec squash₁ go s)
    where
    go : Σ[ y ∈ V ℓ ] (⟨ y ∈ₛ p ⟩ × (z ≡ Ev.eval f (y ∷ vs))) → ∥ D ∥₁
    go (y , y∈p , e) = ∣ fib .fst
      , ( cong (λ w → evalC f (w ∷ vs)) (fib .snd)
        ∙ sym (eval-agree f (y ∷ vs)) ∙ sym e ) ∣₁
      where
      fib : Σ[ m ∈ ⟪ p ⟫ ] (⟪ p ⟫↪ m ≡ y)
      fib = ∈-asFiber {a = y} {b = p} (∈S y p y∈p)
```

<!--en-->
## The realization, at the concrete basis

With the telescope discharged, the realization induction runs over the sixteen
basis functions. Its statement of record is unchanged: every Δ₀ formula over a
transitive `u` has a composite whose value is the definable subset on the nose.
<!--zh-->
## 具体基上的领悟

参数表兑付之后，领悟归纳就在十六个基函数之上运行。其存档陈述不变：传递集 `u` 上的每个 Δ₀ 公式都有一个复合，其值恰是那个可定义子集。
<!--/-->

```agda
module Rl (u : V ℓ) (tu : Trans u) = Ev.Realize u tu imgSpecC

realizeC : (u : V ℓ) (tu : Trans u) (φ : Formula ⟪ u ⟫ 1) → Δ₀ φ
         → Σ[ c ∈ Comp 0 ] (Ev.eval c [] ≡ DefOf.defSet u φ)
realizeC u tu φ d = Rl.realize-defSet u tu φ d
```

<!--en-->
## The closure side

A set is in the rud closure of `u` when it lies in some level of the tower
above `u`, and every level at a limit index is closed under the sixteen basis
functions. What the realization hands over is a composite, so the closure side
asks one question of each telescope slot: does the concrete operation keep a
closed set closed? For nine of the ten the answer is a chain of basis
applications, read off the definitions the seals hide. The tenth, the image,
is the standing residue recorded at the end of this chapter.
<!--zh-->
## 闭包一侧

一个集合属于 `u` 的初步闭包，意即它落在 `u` 之上那座塔的某一层里，而极限索引处的每一层都对十六个基函数封闭。领悟交出的是一个复合，故闭包一侧对参数表的每一格只问一个问题：该具体运算是否把封闭集保持为封闭？十格中有九格的答案是一串基函数施用，从封印所藏的定义读出。第十格，即像，是本章末记录的存留项。
<!--/-->

```agda
ConIn : {k : ℕ} → (V ℓ → Type (ℓ-suc ℓ)) → Comp k → Type (ℓ-suc ℓ)
ConIn P (conC x) = P x
ConIn P (varC i) = Unit*
ConIn P (interC a b) = ConIn P a × ConIn P b
ConIn P (diffC a b) = ConIn P a × ConIn P b
ConIn P (unionC a) = ConIn P a
ConIn P (pairC a b) = ConIn P a × ConIn P b
ConIn P (colC a b) = ConIn P a × ConIn P b
ConIn P (chSepC a b c) = ConIn P a × (ConIn P b × ConIn P c)
ConIn P (eqSepC a b c) = ConIn P a × (ConIn P b × ConIn P c)
ConIn P (imgC f a) = ConIn P f × ConIn P a

AllIn : {k : ℕ} → (V ℓ → Type (ℓ-suc ℓ)) → Vec (V ℓ) k → Type (ℓ-suc ℓ)
AllIn P [] = Unit*
AllIn P (v ∷ vs) = P v × AllIn P vs

lookupIn : {k : ℕ} (P : V ℓ → Type (ℓ-suc ℓ)) (i : Fin k) (ws : Vec (V ℓ) k)
         → AllIn P ws → P (lookup i ws)
lookupIn P zero (v ∷ vs) (hv , hs) = hv
lookupIn P (suc i) (v ∷ vs) (hv , hs) = lookupIn P i vs hs

module Closure (J : V ℓ)
  (Jrud : (i : Op16) (a b : V ℓ) → ⟨ a ∈ˢ J ⟩ → ⟨ b ∈ˢ J ⟩ → ⟨ Fof i a b ∈ˢ J ⟩)
  where

  InJ : V ℓ → Type (ℓ-suc ℓ)
  InJ x = ⟨ x ∈ˢ J ⟩

  J-F0 : (a b : V ℓ) → InJ a → InJ b → InJ (F0 a b)
  J-F0 a b ha hb = subst InJ (Fof-f0 a b) (Jrud f0 a b ha hb)

  J-F1 : (a b : V ℓ) → InJ a → InJ b → InJ (F1 a b)
  J-F1 a b ha hb = subst InJ (Fof-f1 a b) (Jrud f1 a b ha hb)

  J-F2 : (a b : V ℓ) → InJ a → InJ b → InJ (F2 a b)
  J-F2 a b ha hb = subst InJ (Fof-f2 a b) (Jrud f2 a b ha hb)

  J-F5 : (a b : V ℓ) → InJ a → InJ b → InJ (F5 a b)
  J-F5 a b ha hb = subst InJ (Fof-f5 a b) (Jrud f5 a b ha hb)

  J-F6 : (a b : V ℓ) → InJ a → InJ b → InJ (F6 a b)
  J-F6 a b ha hb = subst InJ (Fof-f6 a b) (Jrud f6 a b ha hb)

  J-F7 : (a b : V ℓ) → InJ a → InJ b → InJ (F7 a b)
  J-F7 a b ha hb = subst InJ (Fof-f7 a b) (Jrud f7 a b ha hb)

  J-F9 : (a b : V ℓ) → InJ a → InJ b → InJ (F9 a b)
  J-F9 a b ha hb = subst InJ (Fof-f9 a b) (Jrud f9 a b ha hb)

  J-F10 : (a b : V ℓ) → InJ a → InJ b → InJ (F10 a b)
  J-F10 a b ha hb = subst InJ (Fof-f10 a b) (Jrud f10 a b ha hb)

  opaque
    unfolding interOp
    J-inter : (a b : V ℓ) → InJ a → InJ b → InJ (interOp a b)
    J-inter a b ha hb = J-F1 a (F1 a b) ha (J-F1 a b ha hb)

  opaque
    unfolding unionOp
    J-union : (a : V ℓ) → InJ a → InJ (unionOp a)
    J-union a ha = J-F5 a a ha ha

  opaque
    unfolding memOp
    J-mem : (a : V ℓ) → InJ a → InJ (memOp a)
    J-mem a ha = J-F7 a a ha ha

  opaque
    unfolding colOp
    J-col : (a b : V ℓ) → InJ a → InJ b → InJ (colOp a b)
    J-col a b ha hb = J-F10 (colGraph a b) a
      (J-inter (F7 (sUnion a b) (sUnion a b)) (F2 (F0 a a) b)
        (J-F7 (sUnion a b) (sUnion a b) hs hs)
        (J-F2 (F0 a a) b (J-F0 a a ha ha) hb))
      ha
      where
      hs : InJ (sUnion a b)
      hs = J-F5 (F0 (F0 a a) b) (F0 (F0 a a) b) h₀ h₀
        where
        h₀ : InJ (F0 (F0 a a) b)
        h₀ = J-F0 (F0 a a) b (J-F0 a a ha ha) hb

  opaque
    unfolding condOp
    J-cond : (t c : V ℓ) → InJ t → InJ c → InJ (condOp t c)
    J-cond t c ht hc = J-F6 (F2 c t) (F2 c t) h₂ h₂
      where
      h₂ : InJ (F2 c t)
      h₂ = J-F2 c t hc ht

  opaque
    unfolding memWit
    J-memWit : (a b : V ℓ) → InJ a → InJ b → InJ (memWit a b)
    J-memWit a b ha hb = J-inter (F7 (F0 a b) (F0 a b)) (F0 (F9 a b) (F9 a b))
      (J-F7 (F0 a b) (F0 a b) h₀ h₀)
      (J-F0 (F9 a b) (F9 a b) h₉ h₉)
      where
      h₀ : InJ (F0 a b)
      h₀ = J-F0 a b ha hb
      h₉ : InJ (F9 a b)
      h₉ = J-F9 a b ha hb

  opaque
    unfolding eqWit
    J-eqWit : (a b : V ℓ) → InJ a → InJ b → InJ (eqWit a b)
    J-eqWit a b ha hb = J-inter (F0 a a) (F0 b b)
      (J-F0 a a ha ha) (J-F0 b b hb hb)

  opaque
    unfolding chSepOp
    J-chSep : (a b c : V ℓ) → InJ a → InJ b → InJ c → InJ (chSepOp a b c)
    J-chSep a b c ha hb hc = J-cond (memWit a b) c (J-memWit a b ha hb) hc

  opaque
    unfolding eqSepOp
    J-eqSep : (a b c : V ℓ) → InJ a → InJ b → InJ c → InJ (eqSepOp a b c)
    J-eqSep a b c ha hb hc = J-cond (eqWit a b) c (J-eqWit a b ha hb) hc
```

<!--en-->
The composite induction. Every constructor but the image is discharged by the
chain above; the image is the one hypothesis the module takes, and it is the
classical lemma that the rudimentary functions are closed under images, which
this development has not built.
<!--zh-->
复合上的归纳。除像之外的每个构造子都由上面那串清偿；像是本模块所取的那一条假设，它就是「初步函数对取像封闭」这条经典引理，本书尚未建造。
<!--/-->

```agda
  module Eval-J
    (Jimg : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
          → ConIn InJ f → AllIn InJ vs → InJ p → InJ (imgOpC f vs p))
    where

    evalC-in-J : {k : ℕ} (c : Comp k) (ws : Vec (V ℓ) k)
               → ConIn InJ c → AllIn InJ ws → InJ (evalC c ws)
    evalC-in-J (conC x) ws hc hw = hc
    evalC-in-J (varC i) ws hc hw = lookupIn InJ i ws hw
    evalC-in-J (interC a b) ws (ha , hb) hw = J-inter (evalC a ws) (evalC b ws)
      (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw)
    evalC-in-J (diffC a b) ws (ha , hb) hw = J-F1 (evalC a ws) (evalC b ws)
      (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw)
    evalC-in-J (unionC a) ws ha hw = J-union (evalC a ws) (evalC-in-J a ws ha hw)
    evalC-in-J (pairC a b) ws (ha , hb) hw = J-F0 (evalC a ws) (evalC b ws)
      (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw)
    evalC-in-J (colC a b) ws (ha , hb) hw = J-col (evalC a ws) (evalC b ws)
      (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw)
    evalC-in-J (chSepC a b c) ws (ha , hb , hcc) hw =
      J-chSep (evalC a ws) (evalC b ws) (evalC c ws)
        (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw) (evalC-in-J c ws hcc hw)
    evalC-in-J (eqSepC a b c) ws (ha , hb , hcc) hw =
      J-eqSep (evalC a ws) (evalC b ws) (evalC c ws)
        (evalC-in-J a ws ha hw) (evalC-in-J b ws hb hw) (evalC-in-J c ws hcc hw)
    evalC-in-J (imgC f a) ws (hf , ha) hw =
      Jimg f ws (evalC a ws) hf hw (evalC-in-J a ws ha hw)

    switch-⊇ : (u : V ℓ) (tu : Trans u) (φ : Formula ⟪ u ⟫ 1) (d : Δ₀ φ)
             → ConIn InJ (realizeC u tu φ d .fst)
             → InJ (DefOf.defSet u φ)
    switch-⊇ u tu φ d hc = subst InJ
      (sym (eval-agree (realizeC u tu φ d .fst) []) ∙ realizeC u tu φ d .snd)
      (evalC-in-J (realizeC u tu φ d .fst) [] hc tt*)
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
## The constants of a realizing composite

The realization hands back a composite but says nothing about the constants
inside it, and the closure induction asks exactly that question. The answer is
read off the walk itself: every constant the walk plants is either a member of
`u`, coming from a term constant or a parameter, or `u` itself, coming from the
separations and the complements. Because the walk is a plain recursion on the
formula, the certificate is the same recursion with the composites replaced by
their constant contents.
<!--zh-->
## 领悟复合的常量

领悟交回一个复合，却对其中的常量只字未提，而闭包归纳问的正是这件事。答案从行走本身读出：行走所栽的每个常量，要么是 `u` 的成员，来自词项常量或参数，要么就是 `u` 自身，来自诸分离与诸补。由于行走是对公式的朴素递归，这份证书就是同一场递归，只把诸复合换成它们的常量内容。
<!--/-->

```agda
module WalkCon (u : V ℓ) (tu : Trans u) (P : V ℓ → Type (ℓ-suc ℓ))
               (uP : P u) (memP : (x : V ℓ) → ⟨ x ∈ˢ u ⟩ → P x) where
  open Rl u tu
  open Real using ( split; bexComp; ballComp; module Walk )

  ConF : {k : ℕ} → TmC k → Type (ℓ-suc ℓ)
  ConF (free (fcon v)) = P v
  ConF (free (fvar j)) = Unit*
  ConF sep = Unit*

  conFcomp : {k : ℕ} (a : TmF k) → ConF (free a) → ConIn P (fcomp a)
  conFcomp (fcon v) h = h
  conFcomp (fvar j) h = tt*

  conMem : {k : ℕ} (a b : TmC k) → ConF a → ConF b → ConIn P (memComp a b)
  conMem (free a) (free b) ha hb = conFcomp a ha , (conFcomp b hb , uP)
  conMem (free a) sep ha hb = conFcomp a ha , uP
  conMem sep (free b) ha hb = uP , conFcomp b hb
  conMem sep sep ha hb = uP , uP

  conEq : {k : ℕ} (a b : TmC k) → ConF a → ConF b → ConIn P (eqComp a b)
  conEq (free a) (free b) ha hb = conFcomp a ha , (conFcomp b hb , uP)
  conEq (free a) sep ha hb = uP , (conFcomp a ha , conFcomp a ha)
  conEq sep (free b) ha hb = uP , (conFcomp b hb , conFcomp b hb)
  conEq sep sep ha hb = uP

  conWk : {k : ℕ} (a : TmC k) → ConF a → ConF (wk a)
  conWk (free (fcon v)) h = h
  conWk (free (fvar j)) h = tt*
  conWk sep h = tt*

  conBound : {k : ℕ} (a : TmC (suc k)) → ConF a → ConIn P (boundComp a)
  conBound (free a) h = tt* , (conFcomp a h , uP)
  conBound sep h = tt* , uP

  conBex : {k : ℕ} (a : TmC k) (e : Comp (suc k)) → ConF a → ConIn P e
         → ConIn P (bexComp a e)
  conBex a e ha he = (conBound (wk a) (conWk a ha) , he) , uP

  conBall : {k : ℕ} (a : TmC k) (e : Comp (suc k)) → ConF a → ConIn P e
          → ConIn P (ballComp a e)
  conBall a e ha he = uP , conBex a (diffC (conC u) e) ha (uP , he)

  module WC {n : ℕ} (ρ : Fin n → ⟪ u ⟫) where
    open Walk ρ using ( walk; termC; tsplit )

    conTsplit : {k : ℕ} (s : Fin k ⊎ Fin (suc n)) → ConF (tsplit s)
    conTsplit (inl j) = tt*
    conTsplit (inr zero) = tt*
    conTsplit (inr (suc j)) =
      memP (⟪ u ⟫↪ (ρ j)) (∈S (⟪ u ⟫↪ (ρ j)) u (∈ₛ⟪ u ⟫↪ (ρ j)))

    conTermC : (k : ℕ) (t : Term ⟪ u ⟫ (k + suc n)) → ConF (termC k t)
    conTermC k (con c) = memP (⟪ u ⟫↪ c) (∈S (⟪ u ⟫↪ c) u (∈ₛ⟪ u ⟫↪ c))
    conTermC k (var i) = conTsplit (split k i)

    walkCon : (k : ℕ) (φ : Formula ⟪ u ⟫ (k + suc n)) (d : Δ₀ φ)
            → ConIn P (walk k φ d .fst)
    walkCon k (t ∈̇ s) δ-∈ =
      conMem (termC k t) (termC k s) (conTermC k t) (conTermC k s)
    walkCon k (t ≐ s) δ-≐ =
      conEq (termC k t) (termC k s) (conTermC k t) (conTermC k s)
    walkCon k (φ ∧̇ ψ) (δ-∧ d₁ d₂) = walkCon k φ d₁ , walkCon k ψ d₂
    walkCon k (φ ∨̇ ψ) (δ-∨ d₁ d₂) = walkCon k φ d₁ , walkCon k ψ d₂
    walkCon k (φ ⇒̇ ψ) (δ-⇒ d₁ d₂) = uP , (walkCon k φ d₁ , walkCon k ψ d₂)
    walkCon k (¬̇ φ) (δ-¬ d) = uP , walkCon k φ d
    walkCon k ⊤̇ δ-⊤ = uP
    walkCon k ⊥̇ δ-⊥ = uP , uP
    walkCon k (∀̇∈ t φ) (δ-∀∈ d) = conBall (termC k t) (walk (suc k) φ d .fst)
      (conTermC k t) (walkCon (suc k) φ d)
    walkCon k (∃̇∈ t φ) (δ-∃∈ d) = conBex (termC k t) (walk (suc k) φ d .fst)
      (conTermC k t) (walkCon (suc k) φ d)
    walkCon k (∃̇ φ) ()
    walkCon k (∀̇ φ) ()

  realizeCon : (φ : Formula ⟪ u ⟫ 1) (d : Δ₀ φ)
             → ConIn P (realizeC u tu φ d .fst)
  realizeCon φ d = WC.walkCon (λ ()) 0 φ d
```

<!--en-->
## The switch at limit levels

The trunk faces the theorem at limit indices, where the levels are the `J`s and
each is closed under the sixteen basis functions. Fix a limit `α` and a limit
`β` inside it: the smaller level is the transitive set the descriptions and the
realization both speak about, and the larger one is the closure they land in.
The two directions are then the two halves above, read at that pair.
<!--zh-->
## 极限层处的切换

主干在极限索引处面对本定理，那里的诸层就是诸 `J`，每一层都对十六个基函数封闭。固定一个极限 `α` 与它内部的一个极限 `β`：较小的层是描述与领悟共同谈论的那个传递集，较大的层是它们落进去的闭包。两个方向即上面两半在这一对上的读法。
<!--/-->

```agda
transSmall : (w : V ℓ) → Transitive 𝒮ᵥ (λ x → x ∈ˢ w) → Trans w
transSmall w tr x y x∈y y∈w = ∈s x w (tr (∈S x y x∈y) (∈S y w y∈w))

module LimitSwitch (α : V ℓ) (limα : ⟨ isLimit α ⟩)
                   (β : V ℓ) (limβ : ⟨ isLimit β ⟩) (β∈α : ⟨ β ∈ˢ α ⟩) where
  Ju : V ℓ
  Ju = Jset β limβ

  Jα : V ℓ
  Jα = Jset α limα

  Jtr : Transitive 𝒮ᵥ (λ x → x ∈ˢ Ju)
  Jtr = Sset-trans β

  tu : Trans Ju
  tu = transSmall Ju Jtr

  module Cl = Closure Jα (Jset-rud α limα)
  module Ds = Descr Ju Jtr

  Ju∈Jα : ⟨ Ju ∈ˢ Jα ⟩
  Ju∈Jα = Sset-mem {α = α} {β = β} β∈α

  Ju⊆Jα : (x : V ℓ) → ⟨ x ∈ˢ Ju ⟩ → ⟨ x ∈ˢ Jα ⟩
  Ju⊆Jα = Sset-mono {α = α} {β = β} β∈α

  module WCon = WalkCon Ju tu Cl.InJ Ju∈Jα Ju⊆Jα

  module Up (Jimg : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p : V ℓ)
                  → ConIn Cl.InJ f → AllIn Cl.InJ vs → Cl.InJ p
                  → Cl.InJ (imgOpC f vs p)) where
    module EJ = Cl.Eval-J Jimg

    definable→closure : (φ : Formula ⟪ Ju ⟫ 1) (d : Δ₀ φ)
                      → ⟨ DefOf.defSet Ju φ ∈ˢ Jα ⟩
    definable→closure φ d = EJ.switch-⊇ Ju tu φ d (WCon.realizeCon φ d)

  closure→definable : Ds.ImgArm → (x : V ℓ) → ⟨ x ∈ˢ step Ju ⟩
                    → ((v : V ℓ) → ⟨ v ∈ˢ x ⟩ → ⟨ v ∈ˢ Ju ⟩)
                    → ⟨ x ∈ˢ DefOf.Def Ju ⟩
  closure→definable = Ds.switch-⊆
```

<!--en-->
## Recap

The abstract basis is discharged. Nine of the ten telescope slots are chains
of the sixteen basis functions: pairing, difference and the product are the
functions themselves, the union and the membership relation are their
diagonals, intersection is the double difference with one classical spend
(ruling D-7), collection is a slice of the membership relation read by the
one-point image, and the two separations are the domain of a product against
a witness set. The tenth slot, the image over a composite family, is built
directly and specified against the evaluation, which is written here so that
the image inlines at its own constructor. The realization induction therefore
runs at the concrete operations, and the description chapter's five walled
cells are closed by the write lemmas. What the realization does not say about
its own output, that the constants it plants stay inside `u` and `{u}`, is read
back off the walk here, so the closure induction asks nothing of its caller.

Two residues stand, both named and neither silent. The closure side takes the
rud image principle as a hypothesis: that the image of a composite family over
a member of a closed level is again a member. That is the classical lemma that
the rudimentary functions are closed under images, and it is a chapter of its
own. The description side takes the image arm as a hypothesis: the sixteen
descriptions instantiated at a level, including the case where an argument is
the level itself, which the descriptions as delivered do not cover. The two
easy arms, a member of the level and the level itself, are discharged.
<!--zh-->
## 小结

抽象基已兑付。参数表十格中的九格是十六个基函数的串接：配对、差与积就是那些函数本身，并与隶属关系是它们的对角，交是二重差外加一笔经典支出 (裁定 D-7)，收集是隶属关系的一个切片由单点像读出，两种分离则是一个积对着见证集的定义域。第十格，即复合族上的像，直接造出并对着求值定规格，而求值就写在此处，使像在其自身构造子处内联。于是领悟归纳在具体运算上运行，描述章的五格受阻也被写引理封口。领悟对自身输出未曾言说的那件事，即它所栽的常量不出 `u` 与 `{u}`，在此从行走上反读回来，于是闭包归纳对其调用者一无所求。

两项存留，都已具名，无一沉默。闭包一侧取初步取像原则为假设：复合族在封闭层的一个成员上的像仍是该层的成员。那就是「初步函数对取像封闭」这条经典引理，自成一章。描述一侧取像臂为假设：十六条描述在某一层处的实例，包括实参就是该层自身的情形，而现交付的诸描述并不覆盖它。两条容易的臂，即该层的成员与该层自身，已经清偿。
<!--/-->
