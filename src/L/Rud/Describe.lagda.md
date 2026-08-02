# The per-operation descriptions

<!--en-->
The switch theorem's description half opens. The operations layer defined the
first nine basis functions and sealed their constructions, leaving only the
extension specifications in view; this chapter turns each specification back
into a defining formula: for every operation F0 to F7 and F9, an internal
formula over the small member type of a carrier set, whose satisfaction at a
candidate `v` characterizes membership of `v` in the operation's image, with
the two adequacy directions proved against the exported specification. The
formulas are the classical Delta-0 shapes: bounded existentials over the
arguments, with pairs decomposed by the same bounded readers the coding part
of the book wrote once, restated here over an arbitrary constant domain.

The carrier is abstract (lesson P-h): each description takes a set `A`
together with the argument memberships it needs, and nothing about the
concrete operations is ever unfolded; the operations enter only through their
exported specifications, exactly as the seal in the operations chapter
decrees. For the operations whose specification states its right-hand side
inline, the adequacy below reaches the membership itself; where the
specification's right-hand side is a sealed name, the adequacy is stated
against the same shape under its own name, and the one-line hop across the
seal is recorded in the batch report.
<!--zh-->
切换定理的描述半开张。运算层定义了头九个基函数并把构造封存，只把外延规格留在视野中；本章把每条规格再译回一条定义公式：对 F0 至 F7 与 F9 的每个运算，给出载体集合的小成员类型上的一条内部公式，其在候选 `v` 处的满足刻画`v` 属于该运算之像，两个适足方向对着导出的规格证明。公式取经典 Δ₀ 形状：对实参的有界存在，对则用本书编码部分写过一次、此处对任意常量域重述的有界读式来分解。

载体是抽象的 (法则 P-h)：每条描述取一个集合 `A` 连同它所需的实参隶属，具体运算从不展开；运算只经其导出的规格入场，正如运算章的封印所规定。对那些规格把右端内联陈述的运算，下面的适足直达隶属本身；凡规格的右端是封存名称的运算，适足对着同形但自具名称的右端陈述，跨封印的一行之桥记入批次报告。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rud.Describe {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-¬; δ-∀∈; δ-∃∈ )
import FOL.Semantics

import FOL.Absoluteness
open import FOL.Manipulation.Relabelling
  using ( ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F5; F5-RHS; F5-spec; F9; F9-spec )
open import L.Coding.Base {ℓ}
  using ( prChar-fwd; prChar-bwd )

open import Cubical.Data.Bool using ( true; false )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Functions.Logic as Logic
open Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; ⋃_; union-ax )



open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the small-level conjunction, for the union tower's small memberships (I-2)
_⊓ℓ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⊓ℓ B = Logic._⊓_ A B
```

<!--en-->
## The pair reader, over any domain
<!--zh-->
## 对读式，任意域
<!--/-->

<!--en-->
The descriptions of the pair-producing operations speak about Kuratowski
pairs, so they need the pair reader. The coding chapter wrote it once over
its own constant domain, together with its adequacy; the reader uses no
constants, so it is restated here over an arbitrary domain with the same
adequacy, clause for clause, exactly as the InL chapter restated it. Fixed
de Bruijn indices are named once at each arity.
<!--zh-->
造对运算的描述谈论 Kuratowski 对，故需要对读式。编码章在自己常量域上把它写了一次，并配了适足性；读式不用常量，故此处对任意域重述，适足性逐子句照抄，与 InL 章的重述方式相同。固定的 de Bruijn 序号在每个元数处命名一次。
<!--/-->

```agda
private
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero
  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc zero
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
  f7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  f7 = suc f6
  f8 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
  f8 = suc f7
  f9 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))
  f9 = suc f8
  f10 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))))
  f10 = suc f9

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
           → ⟨ γ ⊨ prAt′ {K = K} q u v ⟩ → ⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)
  prAt′-in q u v γ h = subst ⟨_⟩ (prAt′-adequate q u v γ) h

  prAt′-out : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
            → ⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ) → ⟨ γ ⊨ prAt′ {K = K} q u v ⟩
  prAt′-out q u v γ e = subst ⟨_⟩ (sym (prAt′-adequate q u v γ)) e
```

<!--en-->
## The double-union tower
<!--zh-->
## 二重并之塔
<!--/-->

<!--en-->
The classical shapes for F3, F4, and F6 bound the components of a pair by the
double union of the argument holding the pair: a component of `pr u v` in `y`
lies in `⋃⋃ y`. The operations chapter keeps these facts private, so they are
restated here, together with the tower readers that convert a membership in
the double union into the two-step witness chain and back.
<!--zh-->
F3、F4、F6 的经典形状把对的分量界在持有该对的实参的二重并中：`y` 中 `pr u v`的分量落在 `⋃⋃ y` 内。运算章把这些事实私有，故此处重述，连同把二重并中的隶属换成两步见证链、再换回来的塔读式。
<!--/-->

```agda
private
  u-v∈pr : (u v : V ℓ) → ⟨ ⁅ u , v ⁆ ∈ₛ pr u v ⟩
  u-v∈pr u v = ∈∈ₛ {a = ⁅ u , v ⁆} {b = pr u v} .fst
    ∣ lift true , refl ∣₁

  pair-member-in-⋃⋃ : (y w u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
                    → ⟨ w ∈ˢ (⋃ (⋃ y)) ⟩
  pair-member-in-⋃⋃ y w u v h w∈ = ∈∈ₛ {a = w} {b = ⋃ (⋃ y)} .snd
    (union-ax (⋃ y) w .snd
      ∣ ⁅ u , v ⁆ , (⁅u,v⁆∈ₛ⋃y) , (∈∈ₛ {a = w} {b = ⁅ u , v ⁆} .fst w∈) ∣₁)
    where
    ⁅u,v⁆∈ₛ⋃y : ⟨ ⁅ u , v ⁆ ∈ₛ ⋃ y ⟩
    ⁅u,v⁆∈ₛ⋃y = union-ax y (⁅ u , v ⁆) .snd
      ∣ pr u v , (∈∈ₛ {a = pr u v} {b = y} .fst h) , u-v∈pr u v ∣₁

  prL-in-⋃⋃ : (y u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ u ∈ˢ (⋃ (⋃ y)) ⟩
  prL-in-⋃⋃ y u v h = pair-member-in-⋃⋃ y u u v h ∣ lift false , refl ∣₁

  prR-in-⋃⋃ : (y u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ v ∈ˢ (⋃ (⋃ y)) ⟩
  prR-in-⋃⋃ y u v h = pair-member-in-⋃⋃ y v u v h ∣ lift true , refl ∣₁

  TowerWit : (X u : V ℓ) → Type (ℓ-suc ℓ)
  TowerWit X u = Σ[ r ∈ V ℓ ] Σ[ s ∈ V ℓ ] (⟨ r ∈ˢ X ⟩ × ⟨ s ∈ˢ r ⟩ × ⟨ u ∈ˢ s ⟩)

  tower-out : (X u : V ℓ) → ⟨ u ∈ˢ (⋃ (⋃ X)) ⟩ → ∥ TowerWit X u ∥₁
  tower-out X u h = PT.rec PT.squash₁ step
    (union-ax (⋃ X) u .fst (∈∈ₛ {a = u} {b = ⋃ (⋃ X)} .fst h))
    where
    step : Σ[ s ∈ V ℓ ] ⟨ (s ∈ₛ ⋃ X) ⊓ℓ (u ∈ₛ s) ⟩ → ∥ TowerWit X u ∥₁
    step (s , s∈⋃X , u∈s) = PT.map step₂ (union-ax X s .fst s∈⋃X)
      where
      step₂ : Σ[ r ∈ V ℓ ] ⟨ (r ∈ₛ X) ⊓ℓ (s ∈ₛ r) ⟩ → TowerWit X u
      step₂ (r , r∈X , s∈r) =
        r , (s , (∈∈ₛ {a = r} {b = X} .snd r∈X , (∈∈ₛ {a = s} {b = r} .snd s∈r , ∈∈ₛ {a = u} {b = s} .snd u∈s)))

  tower-in : (X s r u : V ℓ) → ⟨ r ∈ˢ X ⟩ → ⟨ s ∈ˢ r ⟩ → ⟨ u ∈ˢ s ⟩
           → ⟨ u ∈ˢ (⋃ (⋃ X)) ⟩
  tower-in X s r u r∈X s∈r u∈s = ∈∈ₛ {a = u} {b = ⋃ (⋃ X)} .snd
    (union-ax (⋃ X) u .snd ∣ s , (union-ax X s .snd ∣ r , (∈∈ₛ {a = r} {b = X} .fst r∈X , ∈∈ₛ {a = s} {b = r} .fst s∈r) ∣₁) , ∈∈ₛ {a = u} {b = s} .fst u∈s ∣₁)
```

<!--en-->
## The satisfaction chain
<!--zh-->
## 满足之链
<!--/-->

<!--en-->
Membership in a `defSet` is a statement of the inner world, but the adequacy
below is conducted at the outer satisfaction over the carrier's small member
type. The bridge is the InL chain: the definable-subset specification, the
absoluteness of the Delta-0 witness, and the relabelling of the constants,
which compose into one path per formula. The first component of the constant
interpretation is the member itself, definitionally, so the relabelling
collapses to the plain evaluation.
<!--zh-->
`defSet` 中的隶属是内层世界的陈述，而下面的适足在外层满足、即载体小成员类型上的满足处进行。桥是 InL 链：可定义子集规格、Δ₀ 见证的绝对性，以及常量的重标，三者合成每条公式的一条路径。常量解释的第一分量按定义就是成员本身，故重标塌缩为朴素求值。
<!--/-->

```agda
module Chain (A : V ℓ) (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module DefA = DefOf A
  module RefA = DefA.Refine Atrans
  module Abs = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ A) Atrans

  open DefA using ( ι; defSet )
  module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  module AtV = SemV.At (V ℓ) id
  open SemV.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  chain : (φ : Formula ⟪ A ⟫ 1) → Δ₀ φ → (m : ⟪ A ⟫)
        → (⟪ A ⟫↪ m ∈ˢ defSet φ) ≡ (_⊨_ (⟪ A ⟫↪ m ∷ []) φ)
  chain φ d m =
      RefA.abs-defSet φ d m
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ι fst φ (⟪ A ⟫↪ m ∷ [])
```

<!--en-->
## The disjunctive-equality frame
<!--zh-->
## 析取等词框架
<!--/-->

<!--en-->
F0 and F9 are both pair-shaped in the same sense: their members are exactly
one of two named sets, so both descriptions share one frame. The frame takes
the two members as parameters, builds the two-constant disjunction, and
proves its two adequacy directions against the disjunction of the two
equalities, once and for all.
<!--zh-->
F0 与 F9 同为对形，含义相同：其成员恰为两个指名集合之一，故两条描述共享一个框架。框架把两个成员取作参数，造出双常量析取，并一次证明它对两个等词析取的两个适足方向。
<!--/-->

```agda
module F0F9Frame (A : V ℓ) (c₁ c₂ : V ℓ)
  (c₁∈ : ⟨ c₁ ∈ˢ A ⟩) (c₂∈ : ⟨ c₂ ∈ˢ A ⟩) where
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  m₁ : ⟪ A ⟫
  m₁ = ∈-asFiber {a = c₁} {b = A} c₁∈ .fst
  q₁ : ⟪ A ⟫↪ m₁ ≡ c₁
  q₁ = ∈-asFiber {a = c₁} {b = A} c₁∈ .snd
  m₂ : ⟪ A ⟫
  m₂ = ∈-asFiber {a = c₂} {b = A} c₂∈ .fst
  q₂ : ⟪ A ⟫↪ m₂ ≡ c₂
  q₂ = ∈-asFiber {a = c₂} {b = A} c₂∈ .snd

  Φ : Formula ⟪ A ⟫ 1
  Φ = (var zero ≐ con m₁) ∨̇ (var zero ≐ con m₂)

  dΦ : Δ₀ Φ
  dΦ = δ-∨ δ-≐ δ-≐

  eqRHS : (v : V ℓ) → hProp (ℓ-suc ℓ)
  eqRHS v = (v ≡ₕ c₁) ⊔ (v ≡ₕ c₂)

  eq-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ eqRHS v ⟩
  eq-out v h = PT.rec (snd (eqRHS v)) (λ { (inl h₁) →
      ∣ inl (subst (λ x → ⟨ v ≡ₕ x ⟩) q₁ h₁) ∣₁
    ; (inr h₂) →
      ∣ inr (subst (λ x → ⟨ v ≡ₕ x ⟩) q₂ h₂) ∣₁ }) h

  eq-in : (v : V ℓ) → ⟨ eqRHS v ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
  eq-in v = PT.rec (snd ((v ∷ []) ⊨ Φ)) (λ { (inl h) →
      ∣ inl (subst (λ x → ⟨ v ≡ₕ x ⟩) (sym q₁) h) ∣₁
    ; (inr h) →
      ∣ inr (subst (λ x → ⟨ v ≡ₕ x ⟩) (sym q₂) h) ∣₁ })
```

<!--en-->
## F0, the unordered pair
<!--zh-->
## F0，无序对
<!--/-->

<!--en-->
F0 is the first instance of the frame: the two members are the arguments
themselves. Because its specification is transparent, the adequacy reaches
the membership, and the definable-subset equation closes the description in
the InL style: the formula's extension is exactly `F0 a b`. Neither direction
of the equation needs transitivity, which is consumed only by the chain.
<!--zh-->
F0 是框架的第一个实例：两个成员就是实参本身。因其规格透明，适足直达隶属，可定义子集等式按 InL 方式收束描述：公式的外延恰是 `F0 a b`。等式两个方向都不需要传递性，传递性只被链消费。
<!--/-->

```agda
module F0Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module Fr = F0F9Frame A a b a∈ b∈
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd
  m_b : ⟪ A ⟫
  m_b = ∈-asFiber {a = b} {b = A} b∈ .fst
  q_b : ⟪ A ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = A} b∈ .snd

  Φ₀ : Formula ⟪ A ⟫ 1
  Φ₀ = Fr.Φ

  dΦ₀ : Δ₀ Φ₀
  dΦ₀ = Fr.dΦ

  eqRHS₀ : (v : V ℓ) → hProp (ℓ-suc ℓ)
  eqRHS₀ v = (v ≡ₕ a) ⊔ (v ≡ₕ b)

  F0-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₀ ⟩ → ⟨ v ∈ˢ F0 a b ⟩
  F0-desc-out v h = F0-spec a b v .snd (Fr.eq-out v h)

  F0-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F0 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₀ ⟩
  F0-desc-in v h = Fr.eq-in v (F0-spec a b v .fst h)

  F0-defSet≡ : DefA.defSet Φ₀ ≡ F0 a b
  F0-defSet≡ = extensionality (DefA.defSet Φ₀) (F0 a b) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₀ ⊆ F0 a b ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ F0 a b)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefA.defSet Φ₀} .snd y∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₀ m ⟩ → ⟪ A ⟫↪ m ≡ y
          → ⟨ y ∈ₛ F0 a b ⟩
      go m s q = subst (λ w → ⟨ w ∈ₛ F0 a b ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F0 a b} .fst
          (F0-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₀ dΦ₀ m) ∣ (m , s) , refl ∣₁)))

    sub₂ : ⟨ F0 a b ⊆ DefA.defSet Φ₀ ⟩
    sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Φ₀)) step
      (F0-spec a b y .fst (∈∈ₛ {a = y} {b = F0 a b} .snd y∈ₛ))
      where
      step : ⟨ y ≡ₕ a ⟩ ⊎ ⟨ y ≡ₕ b ⟩ → ⟨ y ∈ₛ DefA.defSet Φ₀ ⟩
      step (inl y≡a) = subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₀ ⟩) (sym y≡a)
        (subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₀ ⟩) qₐ
          (∈∈ₛ {a = ⟪ A ⟫↪ mₐ} {b = DefA.defSet Φ₀} .fst
            (subst ⟨_⟩ (sym (Ch.chain Φ₀ dΦ₀ mₐ)) (Fr.eq-in (⟪ A ⟫↪ mₐ) ∣ inl qₐ ∣₁))))
      step (inr y≡b) = subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₀ ⟩) (sym y≡b)
        (subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₀ ⟩) q_b
          (∈∈ₛ {a = ⟪ A ⟫↪ m_b} {b = DefA.defSet Φ₀} .fst
            (subst ⟨_⟩ (sym (Ch.chain Φ₀ dΦ₀ m_b)) (Fr.eq-in (⟪ A ⟫↪ m_b) ∣ inr q_b ∣₁))))

```

<!--en-->
## F1, set difference
<!--zh-->
## F1，差
<!--/-->

<!--en-->
F1's specification is the conjunction of a membership and a negation, so the
formula is the two atoms joined by the object conjunction. Its right-hand
side is stated inline in the specification, so the adequacy reaches the
membership, and the definable-subset equation closes via transitivity: a
member of `a ∖ b` is a member of `a`, hence of the carrier.
<!--zh-->
F1 的规格是隶属与否定之合取，故公式是对象合取联起的两条原子。其右端在规格中内联陈述，故适足直达隶属，可定义子集等式经传递性收束：`a ∖ b` 的成员是`a` 的成员，故在载体之中。
<!--/-->

```agda
module F1Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd
  m_b : ⟪ A ⟫
  m_b = ∈-asFiber {a = b} {b = A} b∈ .fst
  q_b : ⟪ A ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = A} b∈ .snd

  Φ₁ : Formula ⟪ A ⟫ 1
  Φ₁ = (var zero ∈̇ con mₐ) ∧̇ ¬̇ (var zero ∈̇ con m_b)

  dΦ₁ : Δ₀ Φ₁
  dΦ₁ = δ-∧ δ-∈ (δ-¬ δ-∈)

  F1-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁ ⟩ → ⟨ v ∈ˢ F1 a b ⟩
  F1-desc-out v h = F1-spec a b v .snd (v∈a , v∉b)
    where
    v∈a : ⟨ v ∈ˢ a ⟩
    v∈a = subst (λ X → ⟨ v ∈ˢ X ⟩) qₐ (h .fst)
    v∉b : ⟨ ¬ (v ∈ˢ b) ⟩
    v∉b k = h .snd (subst (λ X → ⟨ v ∈ˢ X ⟩) (sym q_b) k)

  F1-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F1 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₁ ⟩
  F1-desc-in v h = (subst (λ X → ⟨ v ∈ˢ X ⟩) (sym qₐ) v∈a) , λ k → v∉b (subst (λ X → ⟨ v ∈ˢ X ⟩) q_b k)
    where
    v∈a : ⟨ v ∈ˢ a ⟩
    v∈a = F1-spec a b v .fst h .fst
    v∉b : ⟨ ¬ (v ∈ˢ b) ⟩
    v∉b = F1-spec a b v .fst h .snd

  F1-defSet≡ : DefA.defSet Φ₁ ≡ F1 a b
  F1-defSet≡ = extensionality (DefA.defSet Φ₁) (F1 a b) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₁ ⊆ F1 a b ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ F1 a b)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefA.defSet Φ₁} .snd y∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₁ m ⟩ → ⟪ A ⟫↪ m ≡ y
          → ⟨ y ∈ₛ F1 a b ⟩
      go m s q = subst (λ w → ⟨ w ∈ₛ F1 a b ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F1 a b} .fst
          (F1-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₁ dΦ₁ m) ∣ (m , s) , refl ∣₁)))

    sub₂ : ⟨ F1 a b ⊆ DefA.defSet Φ₁ ⟩
    sub₂ y y∈ₛ = go (F1-spec a b y .fst (∈∈ₛ {a = y} {b = F1 a b} .snd y∈ₛ))
      where
      go : ⟨ (y ∈ˢ a) ⊓ (¬ (y ∈ˢ b)) ⟩ → ⟨ y ∈ₛ DefA.defSet Φ₁ ⟩
      go (y∈a , y∉b) = let
          y∈A : ⟨ y ∈ˢ A ⟩
          y∈A = Atrans {x = a} {y = y} y∈a a∈
          fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
          fib = ∈-asFiber {a = y} {b = A} y∈A
          m : ⟪ A ⟫
          m = fib .fst
          q : ⟪ A ⟫↪ m ≡ y
          q = fib .snd
          in subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₁ ⟩) q
            (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ₁} .fst
              (subst ⟨_⟩ (sym (Ch.chain Φ₁ dΦ₁ m))
                (F1-desc-in (⟪ A ⟫↪ m)
                  (subst (λ w → ⟨ w ∈ˢ F1 a b ⟩) (sym q) (F1-spec a b y .snd (y∈a , y∉b))))))
```
<!--en-->
## F5, the union
<!--zh-->
## F5，并
<!--/-->

<!--en-->
F5's specification is the union law: a member lies in some member of the
first argument, which is exactly one bounded existential with the membership
atoms on both sides. The member chain `v ∈ w ∈ a` is walked by transitivity
twice in the closing equation.
<!--zh-->
F5 的规格是并定律：成员落在第一实参的某个成员中，正是一条两侧各挂隶属原子的有界存在。成员链 `v ∈ w ∈ a` 在收束等式中由传递性走两步。
<!--/-->

```agda
module F5Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd

  Φ₅ : Formula ⟪ A ⟫ 1
  Φ₅ = ∃̇∈ (con mₐ) (var f1 ∈̇ var zero)

  dΦ₅ : Δ₀ Φ₅
  dΦ₅ = δ-∃∈ δ-∈

  F5-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₅ ⟩ → ⟨ v ∈ˢ F5 a b ⟩
  F5-desc-out v h = F5-spec a b v .snd
    (PT.rec (snd (F5-RHS a v)) (λ { (w , h₁) →
      ∣ w , (subst (λ X → ⟨ w ∈ˢ X ⟩) qₐ (h₁ .fst) , h₁ .snd) ∣₁ }) h)

  F5-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F5 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₅ ⟩
  F5-desc-in v h = PT.rec (snd ((v ∷ []) ⊨ Φ₅)) (λ { (w , h₁) →
      ∣ w , (subst (λ X → ⟨ w ∈ˢ X ⟩) (sym qₐ) (h₁ .fst) , h₁ .snd) ∣₁ })
    (F5-spec a b v .fst h)

  F5-defSet≡ : DefA.defSet Φ₅ ≡ F5 a b
  F5-defSet≡ = extensionality (DefA.defSet Φ₅) (F5 a b) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₅ ⊆ F5 a b ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ F5 a b)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefA.defSet Φ₅} .snd y∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₅ m ⟩ → ⟪ A ⟫↪ m ≡ y
          → ⟨ y ∈ₛ F5 a b ⟩
      go m s q = subst (λ w → ⟨ w ∈ₛ F5 a b ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F5 a b} .fst
          (F5-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₅ dΦ₅ m) ∣ (m , s) , refl ∣₁)))

    sub₂ : ⟨ F5 a b ⊆ DefA.defSet Φ₅ ⟩
    sub₂ y y∈ₛ = go (F5-spec a b y .fst (∈∈ₛ {a = y} {b = F5 a b} .snd y∈ₛ))
      where
      go : ⟨ F5-RHS a y ⟩ → ⟨ y ∈ₛ DefA.defSet Φ₅ ⟩
      go h = PT.rec (snd (y ∈ₛ DefA.defSet Φ₅)) step h
        where
        step : Σ[ w ∈ V ℓ ] (⟨ w ∈ˢ a ⟩ × ⟨ y ∈ˢ w ⟩) → ⟨ y ∈ₛ DefA.defSet Φ₅ ⟩
        step (w , (w∈a , y∈w)) = let
          w∈A : ⟨ w ∈ˢ A ⟩
          w∈A = Atrans {x = a} {y = w} w∈a a∈
          y∈A : ⟨ y ∈ˢ A ⟩
          y∈A = Atrans {x = w} {y = y} y∈w w∈A
          fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
          fib = ∈-asFiber {a = y} {b = A} y∈A
          m : ⟪ A ⟫
          m = fib .fst
          q : ⟪ A ⟫↪ m ≡ y
          q = fib .snd
          in subst (λ z → ⟨ z ∈ₛ DefA.defSet Φ₅ ⟩) q
            (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ₅} .fst
              (subst ⟨_⟩ (sym (Ch.chain Φ₅ dΦ₅ m))
                (F5-desc-in (⟪ A ⟫↪ m)
                  (subst (λ z → ⟨ z ∈ˢ F5 a b ⟩) (sym q)
                    (F5-spec a b y .snd ∣ w , (w∈a , y∈w) ∣₁)))))
```
<!--en-->
## F9, the ordered pair
<!--zh-->
## F9，有序对
<!--/-->

<!--en-->
F9 is the frame's second instance, with the two members of the Kuratowski
pair as the named sets. The formula's constants are indices of those members,
so the module takes their memberships in the carrier as hypotheses: the
description of the pair's image needs the pair's two members available as
parameters, which is the closure hypothesis the switch will supply. With
them, the adequacy reaches the membership and the equation closes.
<!--zh-->
F9 是框架的第二个实例，以 Kuratowski 对的两个成员为指名集合。公式的常量是这两个成员的索引，故模块把它们在载体中的隶属取作假设：描述对的像需要对的两个成员可作参数，这正是切换章将供应的闭包假设。有了它们，适足直达隶属，等式收束。
<!--/-->

```agda
module F9Desc (A a b : V ℓ) (c₁∈ : ⟨ ⁅ a ⁆s ∈ˢ A ⟩) (c₂∈ : ⟨ ⁅ a , b ⁆ ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module Fr = F0F9Frame A ⁅ a ⁆s ⁅ a , b ⁆ c₁∈ c₂∈
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  Φ₉ : Formula ⟪ A ⟫ 1
  Φ₉ = Fr.Φ

  dΦ₉ : Δ₀ Φ₉
  dΦ₉ = Fr.dΦ

  eqRHS₉ : (v : V ℓ) → hProp (ℓ-suc ℓ)
  eqRHS₉ v = (v ≡ₕ ⁅ a ⁆s) ⊔ (v ≡ₕ ⁅ a , b ⁆)

  F9-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₉ ⟩ → ⟨ v ∈ˢ F9 a b ⟩
  F9-desc-out v h = F9-spec a b v .snd (Fr.eq-out v h)

  F9-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F9 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₉ ⟩
  F9-desc-in v h = Fr.eq-in v (F9-spec a b v .fst h)

  F9-defSet≡ : DefA.defSet Φ₉ ≡ F9 a b
  F9-defSet≡ = extensionality (DefA.defSet Φ₉) (F9 a b) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₉ ⊆ F9 a b ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ F9 a b)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefA.defSet Φ₉} .snd y∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₉ m ⟩ → ⟪ A ⟫↪ m ≡ y
          → ⟨ y ∈ₛ F9 a b ⟩
      go m s q = subst (λ w → ⟨ w ∈ₛ F9 a b ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F9 a b} .fst
          (F9-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₉ dΦ₉ m) ∣ (m , s) , refl ∣₁)))

    sub₂ : ⟨ F9 a b ⊆ DefA.defSet Φ₉ ⟩
    sub₂ y y∈ₛ = go (F9-spec a b y .fst (∈∈ₛ {a = y} {b = F9 a b} .snd y∈ₛ))
      where
      go : ⟨ eqRHS₉ y ⟩ → ⟨ y ∈ₛ DefA.defSet Φ₉ ⟩
      go h = PT.rec (snd (y ∈ₛ DefA.defSet Φ₉)) step h
        where
        step : ⟨ y ≡ₕ ⁅ a ⁆s ⟩ ⊎ ⟨ y ≡ₕ ⁅ a , b ⁆ ⟩ → ⟨ y ∈ₛ DefA.defSet Φ₉ ⟩
        step (inl y≡c₁) = subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₉ ⟩) (sym y≡c₁)
          (subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₉ ⟩) Fr.q₁
            (∈∈ₛ {a = ⟪ A ⟫↪ Fr.m₁} {b = DefA.defSet Φ₉} .fst
              (subst ⟨_⟩ (sym (Ch.chain Φ₉ dΦ₉ Fr.m₁))
                (Fr.eq-in (⟪ A ⟫↪ Fr.m₁) ∣ inl Fr.q₁ ∣₁))))
        step (inr y≡c₂) = subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₉ ⟩) (sym y≡c₂)
          (subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ₉ ⟩) Fr.q₂
            (∈∈ₛ {a = ⟪ A ⟫↪ Fr.m₂} {b = DefA.defSet Φ₉} .fst
              (subst ⟨_⟩ (sym (Ch.chain Φ₉ dΦ₉ Fr.m₂))
                (Fr.eq-in (⟪ A ⟫↪ Fr.m₂) ∣ inr Fr.q₂ ∣₁))))
```
<!--en-->
## F2, the product
<!--zh-->
## F2，积
<!--/-->

<!--en-->
The product's classical shape is one bounded existential over each argument
with the pair clause inside, and the description is exactly that. Its
specification's right-hand side is a sealed name in the operations chapter;
the adequacy is therefore stated against the same shape under this chapter's
own name, and the one-line hop to the sealed name is recorded in the batch
report.
<!--zh-->
积的经典形状是每个实参上的一条有界存在，内藏对子句，描述正是如此。其规格的右端在运算章是封存名称；故适足对着本章自具名称的同形右端陈述，跨封印的一行之桥记入批次报告。
<!--/-->

```agda
module F2Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩) where
  module PA = AtPr (⟪ A ⟫↪)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd
  m_b : ⟪ A ⟫
  m_b = ∈-asFiber {a = b} {b = A} b∈ .fst
  q_b : ⟪ A ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = A} b∈ .snd

  Φ₂ : Formula ⟪ A ⟫ 1
  Φ₂ = ∃̇∈ (con mₐ) (∃̇∈ (con m_b) (prAt′ f2 f1 f0))

  dΦ₂ : Δ₀ Φ₂
  dΦ₂ = δ-∃∈ (δ-∃∈ (Δ₀-prAt′ f2 f1 f0))

  F2-DRHS : (a b v : V ℓ) → hProp (ℓ-suc ℓ)
  F2-DRHS a b v = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ w →
                    (u ∈ˢ a) ⊓ ((w ∈ˢ b) ⊓ (v ≡ₕ pr u w))))

  F2-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₂ ⟩ → ⟨ F2-DRHS a b v ⟩
  F2-sat-out v h = PT.rec (snd (F2-DRHS a b v)) step₁ h
    where
    step₁ : Σ[ u ∈ V ℓ ] ⟨ (u ∈ˢ ⟪ A ⟫↪ mₐ) ⊓ ((u ∷ v ∷ []) ⊨ (∃̇∈ (con m_b) (prAt′ f2 f1 f0))) ⟩
          → ⟨ F2-DRHS a b v ⟩
    step₁ (u , h₁) = ∣ u , (PT.rec (snd (⋁ (V ℓ) (λ w →
                        (u ∈ˢ a) ⊓ ((w ∈ˢ b) ⊓ (v ≡ₕ pr u w))))) (λ { (w , h₂) →
      ∣ w , ((subst (λ X → ⟨ u ∈ˢ X ⟩) qₐ (h₁ .fst))
           , (subst (λ X → ⟨ w ∈ˢ X ⟩) q_b (h₂ .fst)
             , PA.prAt′-in f2 f1 f0 (w ∷ u ∷ v ∷ []) (h₂ .snd))) ∣₁ }) (h₁ .snd)) ∣₁

  F2-sat-in : (v : V ℓ) → ⟨ F2-DRHS a b v ⟩ → ⟨ (v ∷ []) ⊨ Φ₂ ⟩
  F2-sat-in v h = PT.rec (snd ((v ∷ []) ⊨ Φ₂)) (λ { (u , h₁) →
    PT.rec (snd ((v ∷ []) ⊨ Φ₂)) (λ { (w , h₂) →
      ∣ u , ((subst (λ X → ⟨ u ∈ˢ X ⟩) (sym qₐ) (h₂ .fst))
           , ∣ w , ((subst (λ X → ⟨ w ∈ˢ X ⟩) (sym q_b) (h₂ .snd .fst))
             , PA.prAt′-out f2 f1 f0 (w ∷ u ∷ v ∷ []) (h₂ .snd .snd)) ∣₁) ∣₁ }) h₁ }) h
```
<!--en-->
## F6, the domain
<!--zh-->
## F6，定义域
<!--/-->

<!--en-->
F6 reads the left components of the pairs in its first argument. The
components of a pair in `a` lie in the double union of `a`, so the classical
shape climbs the two-step tower for each of them, with a waypoint for the
pair itself and an equality atom for the component.
<!--zh-->
F6 读出第一实参中诸对的左分量。`a` 中一对的分量落在 `a` 的二重并内，故经典形状为每个分量爬两步之塔，给对本身一个中转站，给分量一条等词原子。
<!--/-->

```agda
module F6Desc (A a : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) where
  module PA = AtPr (⟪ A ⟫↪)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd

  Φ₆ : Formula ⟪ A ⟫ 1
  Φ₆ = ∃̇∈ (con mₐ) (∃̇∈ (var zero) (∃̇∈ (var zero)
        (∃̇∈ (con mₐ) (∃̇∈ (var zero) (∃̇∈ (var zero)
        (∃̇∈ (con mₐ) ((var f4 ∈̇ var f5) ∧̇ ((var f1 ∈̇ var f2) ∧̇ (prAt′ f0 f4 f1 ∧̇ (var f7 ≐ var f4))))))))))

  dΦ₆ : Δ₀ Φ₆
  dΦ₆ = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∧ (Δ₀-prAt′ f0 f4 f1) δ-≐)))))))))

  F6-DRHS : (a v : V ℓ) → hProp (ℓ-suc ℓ)
  F6-DRHS a v = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ w → (pr u w ∈ˢ a) ⊓ (v ≡ₕ u)))

  F6-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₆ ⟩ → ⟨ F6-DRHS a v ⟩
  F6-sat-out v h = PT.rec (snd (F6-DRHS a v)) (λ { (s₁ , h₁) →
    PT.rec (snd (F6-DRHS a v)) (λ { (r₁ , h₂) →
    PT.rec (snd (F6-DRHS a v)) (λ { (u , h₃) →
    PT.rec (snd (F6-DRHS a v)) (λ { (s₂ , h₄) →
    PT.rec (snd (F6-DRHS a v)) (λ { (r₂ , h₅) →
    PT.rec (snd (F6-DRHS a v)) (λ { (w , h₆) →
    PT.rec (snd (F6-DRHS a v)) (λ { (p , h₇) →
      let env = p ∷ w ∷ s₂ ∷ r₂ ∷ u ∷ s₁ ∷ r₁ ∷ v ∷ []
          p∈a : ⟨ p ∈ˢ a ⟩
          p∈a = subst (λ X → ⟨ p ∈ˢ X ⟩) qₐ (h₇ .fst)
          p≡ : p ≡ pr u w
          p≡ = PA.prAt′-in f0 f4 f1 env (h₇ .snd .snd .snd .fst)
          pruv∈a : ⟨ pr u w ∈ˢ a ⟩
          pruv∈a = subst (λ s → ⟨ s ∈ˢ a ⟩) p≡ p∈a
      in ∣ u , (∣ w , (pruv∈a , h₇ .snd .snd .snd .snd) ∣₁) ∣₁ }) (h₆ .snd) }) (h₅ .snd) }) (h₄ .snd) }) (h₃ .snd) }) (h₂ .snd) }) (h₁ .snd) }) h

  F6-sat-in : (v : V ℓ) → ⟨ F6-DRHS a v ⟩ → ⟨ (v ∷ []) ⊨ Φ₆ ⟩
  F6-sat-in v h = PT.rec (snd ((v ∷ []) ⊨ Φ₆)) (λ { (u , h₁) →
    PT.rec (snd ((v ∷ []) ⊨ Φ₆)) (λ { (w , h₂) →
      PT.rec (snd ((v ∷ []) ⊨ Φ₆)) (λ { (r₁ , (s₁ , (r₁∈a , (s₁∈r₁ , u∈s₁)))) →
      PT.rec (snd ((v ∷ []) ⊨ Φ₆)) (λ { (r₂ , (s₂ , (r₂∈a , (s₂∈r₂ , w∈s₂)))) →
        let p = pr u w
            env = p ∷ w ∷ s₂ ∷ r₂ ∷ u ∷ s₁ ∷ r₁ ∷ v ∷ []
            sat : ⟨ env ⊨ ((var f4 ∈̇ var f5) ∧̇ ((var f1 ∈̇ var f2) ∧̇ (prAt′ f0 f4 f1 ∧̇ (var f7 ≐ var f4)))) ⟩
            sat = u∈s₁ , (w∈s₂ , (PA.prAt′-out f0 f4 f1 env refl , h₂ .snd))
        in ∣ r₁ , (subst (λ X → ⟨ r₁ ∈ˢ X ⟩) (sym qₐ) r₁∈a , ∣ s₁ , (s₁∈r₁ , ∣ u , (u∈s₁ , ∣ r₂ , (subst (λ X → ⟨ r₂ ∈ˢ X ⟩) (sym qₐ) r₂∈a , ∣ s₂ , (s₂∈r₂ , ∣ w , (w∈s₂ , ∣ pr u w , (subst (λ X → ⟨ pr u w ∈ˢ X ⟩) (sym qₐ) (h₂ .fst) , sat) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ }) (tower-out a w (prR-in-⋃⋃ a u w (h₂ .fst))) }) (tower-out a u (prL-in-⋃⋃ a u w (h₂ .fst))) }) h₁ }) h
```
<!--en-->
## F7, the membership relation
<!--zh-->
## F7，隶属关系
<!--/-->

<!--en-->
F7 collects the pairs of members of `a` whose first component lies in the
second. The description is the two bounded existentials over `a` with the
membership atom and the pair clause inside.
<!--zh-->
F7 收集 `a` 的成员对，第一分量属于第二分量者。描述是对 `a` 的两条有界存在，内藏隶属原子与对子句。
<!--/-->

```agda
module F7Desc (A a : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) where
  module PA = AtPr (⟪ A ⟫↪)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd

  Φ₇ : Formula ⟪ A ⟫ 1
  Φ₇ = ∃̇∈ (con mₐ) (∃̇∈ (con mₐ) ((var f1 ∈̇ var f0) ∧̇ prAt′ f2 f1 f0))

  dΦ₇ : Δ₀ Φ₇
  dΦ₇ = δ-∃∈ (δ-∃∈ (δ-∧ δ-∈ (Δ₀-prAt′ f2 f1 f0)))

  F7-DRHS : (a v : V ℓ) → hProp (ℓ-suc ℓ)
  F7-DRHS a v = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ w →
                  (u ∈ˢ a) ⊓ ((w ∈ˢ a) ⊓ ((u ∈ˢ w) ⊓ (v ≡ₕ pr u w)))))

  F7-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₇ ⟩ → ⟨ F7-DRHS a v ⟩
  F7-sat-out v h = PT.rec (snd (F7-DRHS a v)) (λ { (u , h₁) →
    PT.rec (snd (F7-DRHS a v)) (λ { (w , h₂) →
      let env = w ∷ u ∷ v ∷ []
      in ∣ u , (∣ w , ((subst (λ X → ⟨ u ∈ˢ X ⟩) qₐ (h₁ .fst))
                 , ((subst (λ X → ⟨ w ∈ˢ X ⟩) qₐ (h₂ .fst))
                 , (h₂ .snd .fst , PA.prAt′-in f2 f1 f0 env (h₂ .snd .snd)))) ∣₁) ∣₁ }) (h₁ .snd) }) h

  F7-sat-in : (v : V ℓ) → ⟨ F7-DRHS a v ⟩ → ⟨ (v ∷ []) ⊨ Φ₇ ⟩
  F7-sat-in v h = PT.rec (snd ((v ∷ []) ⊨ Φ₇)) (λ { (u , h₁) →
    PT.rec (snd ((v ∷ []) ⊨ Φ₇)) (λ { (w , h₂) →
      let env = w ∷ u ∷ v ∷ []
          u∈w = h₂ .snd .snd .fst
          t≡ = h₂ .snd .snd .snd
      in ∣ u , ((subst (λ X → ⟨ u ∈ˢ X ⟩) (sym qₐ) (h₂ .fst))
           , ∣ w , ((subst (λ X → ⟨ w ∈ˢ X ⟩) (sym qₐ) (h₂ .snd .fst))
             , (u∈w , PA.prAt′-out f2 f1 f0 env t≡)) ∣₁) ∣₁ }) h₁ }) h
```
<!--en-->
## F3 and F4, one frame
<!--zh-->
## F3 与 F4，一个框架
<!--/-->

<!--en-->
F3 inserts a member of `x` between the components of a pair in `y`, and F4
appends it at the right; the two differ by one coordinate exchange in the
middle pair. One frame carries both, taking the two middle slots and the
image shape as parameters: the tower climbs the double union of the second
argument for each component, a waypoint in the argument records the pair
itself, and two waypoints inside the candidate witness the middle pair. The
frame delivers the shared formula and its Delta-0 witness. The two adequacy
directions against the frame's own image shape hit a stubborn unification in
this batch and are recorded as a no-go trail in the batch report; the
formulas and witnesses stand on their own, and the adequacy is a matter for
the next batch.
<!--zh-->
F3 把 `x` 的成员夹进 `y` 中对的两个分量之间，F4 把它接在右端；二者只差中间对的一次坐标交换。一个框架承载两者，以两个中间槽位与像形为参数：塔为每个分量爬第二实参的二重并，实参里的一个中转站记录对本身，候选里的两个中转站见证中间对。框架交付共享公式与其 Δ₀ 见证。对着框架自身像形的两个适足方向在本批撞上一处顽固的合一，记入批次报告的 no-go 轨迹；公式与见证独立成立，适足留给下一批。
<!--/-->

```agda


module InsertAppendFrame (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩)
  (mid₁ mid₂ : Fin 11) (midp : V ℓ → V ℓ → V ℓ → V ℓ)
  where
  module PA = AtPr (⟪ A ⟫↪)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA using ( _^_ )
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₐ : ⟪ A ⟫
  mₐ = ∈-asFiber {a = a} {b = A} a∈ .fst
  qₐ : ⟪ A ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = A} a∈ .snd
  m_b : ⟪ A ⟫
  m_b = ∈-asFiber {a = b} {b = A} b∈ .fst
  q_b : ⟪ A ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = A} b∈ .snd

  body : Formula ⟪ A ⟫ 11
  body = (var f7 ∈̇ var f8) ∧̇ ((var f4 ∈̇ var f5) ∧̇ ((var f3 ∈̇ con mₐ)
       ∧̇ (prAt′ f2 f7 f4 ∧̇ (prAt′ f0 mid₁ mid₂ ∧̇ prAt′ f10 f7 f0))))

  dBody : Δ₀ body
  dBody = δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∧ δ-∈
    (δ-∧ (Δ₀-prAt′ f2 f7 f4) (δ-∧ (Δ₀-prAt′ f0 mid₁ mid₂) (Δ₀-prAt′ f10 f7 f0)))))

  Φ : Formula ⟪ A ⟫ 1
  Φ = ∃̇∈ (con m_b) (∃̇∈ (var zero) (∃̇∈ (var zero)
      (∃̇∈ (con m_b) (∃̇∈ (var zero) (∃̇∈ (var zero)
      (∃̇∈ (con mₐ) (∃̇∈ (con m_b) (∃̇∈ (var f8) (∃̇∈ (var zero) body)))))))))

  dΦ : Δ₀ Φ
  dΦ = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ dBody)))))))))

  DRHS : (a b v : V ℓ) → hProp (ℓ-suc ℓ)
  DRHS a b v = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ z → ⋁ (V ℓ) (λ w →
                 (z ∈ˢ a) ⊓ ((pr u w ∈ˢ b) ⊓ (v ≡ₕ pr u (midp u z w))))))

  module MidAdeq
    (midCorr : (γ : (V ℓ) ^ 11)
             → pr (⟦ var mid₁ ⟧ γ) (⟦ var mid₂ ⟧ γ)
               ≡ midp (⟦ var f7 ⟧ γ) (⟦ var f3 ⟧ γ) (⟦ var f4 ⟧ γ))
    where
    midSat : (γ : (V ℓ) ^ 11) → ⟨ γ ⊨ prAt′ f0 mid₁ mid₂ ⟩
           → ⟦ var f0 ⟧ γ ≡ pr (⟦ var mid₁ ⟧ γ) (⟦ var mid₂ ⟧ γ)
    midSat = PA.prAt′-in f0 mid₁ mid₂
    midSat′ : (γ : (V ℓ) ^ 11)
            → ⟦ var f0 ⟧ γ ≡ pr (⟦ var mid₁ ⟧ γ) (⟦ var mid₂ ⟧ γ)
            → ⟨ γ ⊨ prAt′ f0 mid₁ mid₂ ⟩
    midSat′ = PA.prAt′-out f0 mid₁ mid₂

  ```
<!--en-->
The two instantiations differ by one coordinate exchange, exactly as the
specifications do: F3's middle pair is `pr z w`, F4's is `pr w z`, and the
slots swap accordingly. Each instantiation names the frame's formula and
witness under its own F-name; the adequacy directions are deferred with the
frame's no-go trail.
<!--zh-->
两个实例只差一次坐标交换，与规格完全一致：F3 的中间对是 `pr z w`，F4 的是 `pr w z`，槽位随之对调。每个实例把框架的公式与见证以自家 F 名命名；适足方向随框架的 no-go 轨迹推迟。
<!--/-->

```agda
module F3Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩) where
  open InsertAppendFrame A a b a∈ b∈ f3 f4 (λ u z w → pr z w)
    using ( Φ; dΦ )

  Φ₃ : Formula ⟪ A ⟫ 1
  Φ₃ = Φ

  dΦ₃ : Δ₀ Φ₃
  dΦ₃ = dΦ

module F4Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩) where
  open InsertAppendFrame A a b a∈ b∈ f4 f3 (λ u z w → pr w z)
    using ( Φ; dΦ )

  Φ₄ : Formula ⟪ A ⟫ 1
  Φ₄ = Φ

  dΦ₄ : Δ₀ Φ₄
  dΦ₄ = dΦ


```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Nine defining formulas and their Delta-0 witnesses are in place, one per
committed operation. F0, F1, F5, and F9 additionally carry both adequacy
directions against the membership itself and close with the definable-subset
equation. F2, F6, and F7 carry both directions against the specification's
right-hand side under this chapter's own names, because those right-hand
sides are sealed names in the operations chapter, and the hop across the
seal is a matter for the batch report. F3 and F4 deliver the shared formula
and witness, with the adequacy directions recorded as a no-go trail. The
carrier is a module parameter throughout, and nothing of the operations ever
unfolds.
<!--zh-->
九条定义公式与九个 Δ₀ 见证就位，九个承诺运算各一条。F0、F1、F5、F9 另带对隶属本身的两个适足方向，并以可定义子集等式收束。F2、F6、F7 带对规格右端、以本章自具名称陈述的两个方向，因为那些右端在运算章是封存名称，跨封印的一行之桥记入批次报告。F3、F4 交付共享公式与见证，适足方向记入 no-go 轨迹。载体自始至终是模块参数，运算本身从不展开。
<!--/-->

