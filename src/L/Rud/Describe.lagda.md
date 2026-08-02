# The per-operation descriptions

<!--en-->
The switch theorem's description half opens. The operations layer defined
the sixteen basis functions and sealed their constructions, leaving only
the extension specifications in view; this chapter turns each specification
back into a defining formula: for every operation F0 to F15, an internal
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
specification's right-hand side is a sealed name, the membership-to-shape
hop goes through the read lemmas the operations chapter appends, and the
reverse direction stays walled by the seal, as recorded in the batch report.
<!--zh-->
切换定理的描述半开张。运算层定义了头九个基函数并把构造封存，只把外延规格留在视野中；本章把每条规格再译回一条定义公式：对 F0 至 F7 与 F9 的每个运算，给出载体集合的小成员类型上的一条内部公式，其在候选 `v` 处的满足刻画`v` 属于该运算之像，两个适足方向对着导出的规格证明。公式取经典 Δ₀ 形状：对实参的有界存在，对则用本书编码部分写过一次、此处对任意常量域重述的有界读式来分解。

载体是抽象的 (法则 P-h)：每条描述取一个集合 `A` 连同它所需的实参隶属，具体运算从不展开；运算只经其导出的规格入场，正如运算章的封印所规定。对那些规格把右端内联陈述的运算，下面的适足直达隶属本身；凡规格的右端是封存名称的运算，从隶属到像形的跳走运算章补加的读引理，反向仍被封印挡着，记入批次报告。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rud.Describe {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-∀∈; δ-∃∈ )
import FOL.Semantics

import FOL.Absoluteness
open import FOL.Manipulation.Relabelling
  using ( ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Ops {ℓ}
  using ( F0; F0-spec; F1; F1-spec; F2; F3; F4; F5; F5-RHS; F5-spec
        ; F6; F7; F9; F9-spec
        ; F2-read; F3-read; F4-read; F6-read; F7-read )
open import L.Rud.Images {ℓ}
  using ( F8; F8-spec; F10; F10-spec; F11; F11-spec; F12; F12-spec
        ; F13; F13-spec; F14; F14-spec; module F15Of )
open import L.Coding.Base {ℓ}
  using ( prChar-fwd; prChar-bwd )

open import Cubical.Data.Bool using ( true; false )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt )
import Cubical.Functions.Logic as Logic
open Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
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

  -- the two members of a Kuratowski pair, as members of the pair set
  singl∈pr : (u v : V ℓ) → ⟨ ⁅ u ⁆s ∈ₛ pr u v ⟩
  singl∈pr u v = ∈∈ₛ {a = ⁅ u ⁆s} {b = pr u v} .fst
    ∣ lift false , refl ∣₁

  pair∈pr : (u v : V ℓ) → ⟨ ⁅ u , v ⁆ ∈ₛ pr u v ⟩
  pair∈pr u v = ∈∈ₛ {a = ⁅ u , v ⁆} {b = pr u v} .fst
    ∣ lift true , refl ∣₁

  a∈singl : (a : V ℓ) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
  a∈singl a = ∈∈ₛ {a = a} {b = ⁅ a ⁆s} .fst ∣ lift tt , refl ∣₁

  a∈pair : (a b : V ℓ) → ⟨ a ∈ₛ ⁅ a , b ⁆ ⟩
  a∈pair a b = ∈∈ₛ {a = a} {b = ⁅ a , b ⁆} .fst
    ∣ lift false , refl ∣₁

  v∈pair : (a b : V ℓ) → ⟨ b ∈ₛ ⁅ a , b ⁆ ⟩
  v∈pair a b = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .fst
    ∣ lift true , refl ∣₁

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

  ⋃⋃-in-A : (A X : V ℓ) → (X∈ : ⟨ X ∈ˢ A ⟩)
           → (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A))
           → (u : V ℓ) → ⟨ u ∈ˢ (⋃ (⋃ X)) ⟩ → ⟨ u ∈ˢ A ⟩
  ⋃⋃-in-A A X X∈ Atrans u h = PT.rec (snd (u ∈ˢ A)) tower (tower-out X u h)
    where
    tower : TowerWit X u → ⟨ u ∈ˢ A ⟩
    tower (r , s , (r∈X , (s∈r , u∈s))) =
      Atrans {x = s} {y = u} u∈s
        (Atrans {x = r} {y = s} s∈r (Atrans {x = X} {y = r} r∈X X∈))
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
specification's right-hand side is a sealed name in the operations chapter,
so the adequacy is stated against the same shape under this chapter's own
name. The read lemma now supplies the membership-to-shape hop: a member of
the product decomposes through the read and reassembles into the chapter's
shape, closing the direction toward the satisfaction; the direction out of
the specification stays walled by the seal and is recorded in the batch
report.
<!--zh-->
积的经典形状是每个实参上的一条有界存在，内藏对子句，描述正是如此。其规格的右端在运算章是封存名称，故适足对着本章自具名称的同形右端陈述。读引理如今供给从隶属到像形的跳：积的成员经读引理拆开，再重组为本章的像形，收束通向满足的方向；出自规格的方向仍被封印挡着，记入批次报告。
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

  F2-mem-DRHS : (v : V ℓ) → ⟨ v ∈ˢ F2 a b ⟩ → ⟨ F2-DRHS a b v ⟩
  F2-mem-DRHS v h = PT.rec (snd (F2-DRHS a b v)) step (F2-read a b v h)
    where
    step : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
             (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p q ⟩)
         → ⟨ F2-DRHS a b v ⟩
    step (p , q , p∈a , q∈b , v≡) = ∣ p , ∣ q , (p∈a , (q∈b , v≡)) ∣₁ ∣₁

  F2-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F2 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₂ ⟩
  F2-desc-in v h = F2-sat-in v (F2-mem-DRHS v h)
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
pair itself and an equality atom for the component. The read lemma closes
the membership-to-shape hop, and the definable-subset inclusion toward the
defSet closes because the component lies in the carrier by transitivity.
<!--zh-->
F6 读出第一实参中诸对的左分量。`a` 中一对的分量落在 `a` 的二重并内，故经典形状为每个分量爬两步之塔，给对本身一个中转站，给分量一条等词原子。读引理收束从隶属到像形的跳，可定义子集朝 defSet 方向的包含因分量经传递性落入载体而收束。
<!--/-->

```agda
module F6Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module PA = AtPr (⟪ A ⟫↪)
  module DefA = DefOf A
  module Ch = Chain A Atrans
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

  F6-mem-DRHS : (v : V ℓ) → ⟨ v ∈ˢ F6 a b ⟩ → ⟨ F6-DRHS a v ⟩
  F6-mem-DRHS v h = PT.rec (snd (F6-DRHS a v)) step (F6-read a b v h)
    where
    step : Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ]
             (⟨ pr u w ∈ˢ a ⟩ × ⟨ v ≡ₕ u ⟩)
         → ⟨ F6-DRHS a v ⟩
    step (u , w , pruw∈a , v≡) = ∣ u , ∣ w , (pruw∈a , v≡) ∣₁ ∣₁

  F6-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F6 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₆ ⟩
  F6-desc-in v h = F6-sat-in v (F6-mem-DRHS v h)

  F6-defSet-in : ⟨ F6 a b ⊆ DefA.defSet Φ₆ ⟩
  F6-defSet-in y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Φ₆)) step
    (F6-read a b y (∈∈ₛ {a = y} {b = F6 a b} .snd y∈ₛ))
    where
    step : Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ]
             (⟨ pr u w ∈ˢ a ⟩ × ⟨ y ≡ₕ u ⟩)
         → ⟨ y ∈ₛ DefA.defSet Φ₆ ⟩
    step (u , w , pruw∈a , y≡) = let
        u∈A : ⟨ u ∈ˢ A ⟩
        u∈A = ⋃⋃-in-A A a a∈ Atrans u (prL-in-⋃⋃ a u w pruw∈a)
        y∈A : ⟨ y ∈ˢ A ⟩
        y∈A = subst (λ z → ⟨ z ∈ˢ A ⟩) (sym y≡) u∈A
        fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
        fib = ∈-asFiber {a = y} {b = A} y∈A
        m : ⟪ A ⟫
        m = fib .fst
        q : ⟪ A ⟫↪ m ≡ y
        q = fib .snd
        in subst (λ z → ⟨ z ∈ₛ DefA.defSet Φ₆ ⟩) q
          (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ₆} .fst
            (subst ⟨_⟩ (sym (Ch.chain Φ₆ dΦ₆ m))
              (F6-sat-in (⟪ A ⟫↪ m)
                (F6-mem-DRHS (⟪ A ⟫↪ m)
                  (subst (λ z → ⟨ z ∈ˢ F6 a b ⟩) (sym q)
                    (∈∈ₛ {a = y} {b = F6 a b} .snd y∈ₛ))))))
```
<!--en-->
## F7, the membership relation
<!--zh-->
## F7，隶属关系
<!--/-->

<!--en-->
F7 collects the pairs of members of `a` whose first component lies in the
second. The description is the two bounded existentials over `a` with the
membership atom and the pair clause inside, and the read lemma closes the
membership-to-shape hop exactly as for F2 and F6.
<!--zh-->
F7 收集 `a` 的成员对，第一分量属于第二分量者。描述是对 `a` 的两条有界存在，内藏隶属原子与对子句，读引理像 F2、F6 那样收束从隶属到像形的跳。
<!--/-->

```agda
module F7Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) where
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

  F7-mem-DRHS : (v : V ℓ) → ⟨ v ∈ˢ F7 a b ⟩ → ⟨ F7-DRHS a v ⟩
  F7-mem-DRHS v h = PT.rec (snd (F7-DRHS a v)) step (F7-read a b v h)
    where
    step : Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ]
             (⟨ u ∈ˢ a ⟩ × ⟨ w ∈ˢ a ⟩ × ⟨ u ∈ˢ w ⟩ × ⟨ v ≡ₕ pr u w ⟩)
         → ⟨ F7-DRHS a v ⟩
    step (u , w , u∈a , w∈a , u∈w , v≡) =
      ∣ u , ∣ w , (u∈a , (w∈a , (u∈w , v≡))) ∣₁ ∣₁

  F7-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F7 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₇ ⟩
  F7-desc-in v h = F7-sat-in v (F7-mem-DRHS v h)
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
two adequacy directions now close in the restructured shape: the middle
clause is read and rebuilt through the pair reader's adequacy with explicit
positions, the waypoint witnesses are threaded through named eliminations
exactly as the tower readers thread theirs, and the satisfaction-to-shape
direction peels the ten bounded existentials one by one. The membership
direction toward the satisfaction closes through the operations chapter's
read lemma; the direction out of the specification remains walled by the
seal on the right-hand side, as it is for F2, F6, and F7.
<!--zh-->
F3 把 `x` 的成员夹进 `y` 中对的两个分量之间，F4 把它接在右端；二者只差中间对的一次坐标交换。一个框架承载两者，以两个中间槽位与像形为参数：塔为每个分量爬第二实参的二重并，实参里的一个中转站记录对本身，候选里的两个中转站见证中间对。两个适足方向在重构后的形状中收束：中间子句经对读式的适足性以显式位置读出再重建，中转见证经具名消去逐一穿线，恰如塔读式穿线那样；满足到像形方向把十条有界存在逐条剥开。通向满足的隶属方向经运算章的读引理收束；出自规格的方向与 F2、F6、F7 一样仍被右端的封印挡着。
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

    sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ DRHS a b v ⟩
    sat-out v h = PT.rec (snd (DRHS a b v)) (λ { (p₁ , h₁) →
      PT.rec (snd (DRHS a b v)) (λ { (s₁ , h₂) →
      PT.rec (snd (DRHS a b v)) (λ { (u , h₃) →
      PT.rec (snd (DRHS a b v)) (λ { (p₂ , h₄) →
      PT.rec (snd (DRHS a b v)) (λ { (s₂ , h₅) →
      PT.rec (snd (DRHS a b v)) (λ { (w , h₆) →
      PT.rec (snd (DRHS a b v)) (λ { (z , h₇) →
      PT.rec (snd (DRHS a b v)) (λ { (p₃ , h₈) →
      PT.rec (snd (DRHS a b v)) (λ { (s₃ , h₉) →
      PT.rec (snd (DRHS a b v)) (λ { (mid , h₁₀) →
        let env = mid ∷ s₃ ∷ p₃ ∷ z ∷ w ∷ s₂ ∷ p₂ ∷ u ∷ s₁ ∷ p₁ ∷ v ∷ []
            z∈a : ⟨ z ∈ˢ a ⟩
            z∈a = subst (λ X → ⟨ z ∈ˢ X ⟩) qₐ (h₇ .fst)
            p₃∈b : ⟨ p₃ ∈ˢ b ⟩
            p₃∈b = subst (λ X → ⟨ p₃ ∈ˢ X ⟩) q_b (h₈ .fst)
            p₃≡ : p₃ ≡ pr u w
            p₃≡ = PA.prAt′-in f2 f7 f4 env (h₁₀ .snd .snd .snd .snd .fst)
            pruw∈b : ⟨ pr u w ∈ˢ b ⟩
            pruw∈b = subst (λ t → ⟨ t ∈ˢ b ⟩) p₃≡ p₃∈b
            v≡ : v ≡ pr u (midp u z w)
            v≡ = PA.prAt′-in f10 f7 f0 env (h₁₀ .snd .snd .snd .snd .snd .snd)
              ∙ cong (λ s → pr u s) (PA.prAt′-in f0 mid₁ mid₂ env
                              (h₁₀ .snd .snd .snd .snd .snd .fst) ∙ midCorr env)
        in ∣ u , ∣ z , ∣ w , (z∈a , (pruw∈b , v≡)) ∣₁ ∣₁ ∣₁ })
        (h₉ .snd) }) (h₈ .snd) }) (h₇ .snd) }) (h₆ .snd) }) (h₅ .snd) })
        (h₄ .snd) }) (h₃ .snd) }) (h₂ .snd) }) (h₁ .snd) }) h

    sat-in : (v : V ℓ) → ⟨ DRHS a b v ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
    sat-in v h = PT.rec (snd ((v ∷ []) ⊨ Φ)) (λ { (u , h₁) →
      PT.rec (snd ((v ∷ []) ⊨ Φ)) (λ { (z , h₂) →
      PT.rec (snd ((v ∷ []) ⊨ Φ)) (λ { (w , h₃) →
      PT.rec (snd ((v ∷ []) ⊨ Φ))
        (λ { (r₁ , s₁ , (r₁∈b , (s₁∈r₁ , u∈s₁))) →
      PT.rec (snd ((v ∷ []) ⊨ Φ))
        (λ { (r₂ , s₂ , (r₂∈b , (s₂∈r₂ , w∈s₂))) →
        let mid = midp u z w
            p₃ = pr u w
            s₃ = ⁅ u , mid ⁆
            env = mid ∷ s₃ ∷ p₃ ∷ z ∷ w ∷ s₂ ∷ r₂ ∷ u ∷ s₁ ∷ r₁ ∷ v ∷ []
            z∈a : ⟨ z ∈ˢ a ⟩
            z∈a = h₃ .fst
            pruw∈b : ⟨ pr u w ∈ˢ b ⟩
            pruw∈b = h₃ .snd .fst
            v≡ : v ≡ pr u (midp u z w)
            v≡ = h₃ .snd .snd
            v≡mid : v ≡ pr u mid
            v≡mid = v≡
            s₃∈v : ⟨ s₃ ∈ˢ v ⟩
            s₃∈v = subst (λ t → ⟨ s₃ ∈ˢ t ⟩) (sym v≡mid)
              (∈∈ₛ {a = s₃} {b = pr u mid} .snd (pair∈pr u mid))
            mid∈s₃ : ⟨ mid ∈ˢ s₃ ⟩
            mid∈s₃ = ∈∈ₛ {a = mid} {b = s₃} .snd (v∈pair u mid)
            sat : ⟨ env ⊨ body ⟩
            sat = u∈s₁ , (w∈s₂ , ( subst (λ X → ⟨ z ∈ˢ X ⟩) (sym qₐ) z∈a
                 , ( PA.prAt′-out f2 f7 f4 env refl
                 , ( PA.prAt′-out f0 mid₁ mid₂ env (sym (midCorr env))
                 , PA.prAt′-out f10 f7 f0 env v≡mid ) ) ) )
        in ∣ r₁ , (subst (λ X → ⟨ r₁ ∈ˢ X ⟩) (sym q_b) r₁∈b
           , ∣ s₁ , (s₁∈r₁ , ∣ u , (u∈s₁ , ∣ r₂ , (subst (λ X → ⟨ r₂ ∈ˢ X ⟩) (sym q_b) r₂∈b
           , ∣ s₂ , (s₂∈r₂ , ∣ w , (w∈s₂ , ∣ z , (subst (λ X → ⟨ z ∈ˢ X ⟩) (sym qₐ) z∈a
           , ∣ p₃ , (subst (λ X → ⟨ p₃ ∈ˢ X ⟩) (sym q_b) pruw∈b
           , ∣ s₃ , (s₃∈v , ∣ mid , (mid∈s₃ , sat) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ }) 
         (tower-out b w (prR-in-⋃⋃ b u w (h₃ .snd .fst))) })
         (tower-out b u (prL-in-⋃⋃ b u w (h₃ .snd .fst))) }) h₂ }) h₁ }) h

  ```
<!--en-->
The two instantiations differ by one coordinate exchange, exactly as the
specifications do: F3's middle pair is `pr z w`, F4's is `pr w z`, and the
slots swap accordingly. Each instantiation names the frame's formula,
witness, both adequacy directions, and the read-based membership hop under
its own F-name.
<!--zh-->
两个实例只差一次坐标交换，与规格完全一致：F3 的中间对是 `pr z w`，F4 的是 `pr w z`，槽位随之对调。每个实例把框架的公式、见证、两个适足方向与基于读引理的隶属跳以自家 F 名命名。
<!--/-->

```agda
module F3Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩) where
  open InsertAppendFrame A a b a∈ b∈ f3 f4 (λ u z w → pr z w)
    using ( Φ; dΦ; DRHS; module MidAdeq )
  module MA = MidAdeq (λ γ → refl)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  Φ₃ : Formula ⟪ A ⟫ 1
  Φ₃ = Φ

  dΦ₃ : Δ₀ Φ₃
  dΦ₃ = dΦ

  F3-DRHS : (a b v : V ℓ) → hProp (ℓ-suc ℓ)
  F3-DRHS a b v = DRHS a b v

  F3-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₃ ⟩ → ⟨ F3-DRHS a b v ⟩
  F3-sat-out v h = MA.sat-out v h

  F3-sat-in : (v : V ℓ) → ⟨ F3-DRHS a b v ⟩ → ⟨ (v ∷ []) ⊨ Φ₃ ⟩
  F3-sat-in v h = MA.sat-in v h

  F3-mem-DRHS : (v : V ℓ) → ⟨ v ∈ˢ F3 a b ⟩ → ⟨ F3-DRHS a b v ⟩
  F3-mem-DRHS v h = PT.rec (snd (F3-DRHS a b v)) step (F3-read a b v h)
    where
    step : Σ[ u ∈ V ℓ ] Σ[ z ∈ V ℓ ] Σ[ w ∈ V ℓ ]
             (⟨ z ∈ˢ a ⟩ × ⟨ pr u w ∈ˢ b ⟩ × ⟨ v ≡ₕ pr u (pr z w) ⟩)
         → ⟨ F3-DRHS a b v ⟩
    step (u , z , w , z∈a , pruw∈b , v≡) =
      ∣ u , ∣ z , ∣ w , (z∈a , (pruw∈b , v≡)) ∣₁ ∣₁ ∣₁

  F3-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F3 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₃ ⟩
  F3-desc-in v h = F3-sat-in v (F3-mem-DRHS v h)

module F4Desc (A a b : V ℓ) (a∈ : ⟨ a ∈ˢ A ⟩) (b∈ : ⟨ b ∈ˢ A ⟩) where
  open InsertAppendFrame A a b a∈ b∈ f4 f3 (λ u z w → pr w z)
    using ( Φ; dΦ; DRHS; module MidAdeq )
  module MA = MidAdeq (λ γ → refl)
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  Φ₄ : Formula ⟪ A ⟫ 1
  Φ₄ = Φ

  dΦ₄ : Δ₀ Φ₄
  dΦ₄ = dΦ

  F4-DRHS : (a b v : V ℓ) → hProp (ℓ-suc ℓ)
  F4-DRHS a b v = DRHS a b v

  F4-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₄ ⟩ → ⟨ F4-DRHS a b v ⟩
  F4-sat-out v h = MA.sat-out v h

  F4-sat-in : (v : V ℓ) → ⟨ F4-DRHS a b v ⟩ → ⟨ (v ∷ []) ⊨ Φ₄ ⟩
  F4-sat-in v h = MA.sat-in v h

  F4-mem-DRHS : (v : V ℓ) → ⟨ v ∈ˢ F4 a b ⟩ → ⟨ F4-DRHS a b v ⟩
  F4-mem-DRHS v h = PT.rec (snd (F4-DRHS a b v)) step (F4-read a b v h)
    where
    step : Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ] Σ[ z ∈ V ℓ ]
             (⟨ z ∈ˢ a ⟩ × ⟨ pr u w ∈ˢ b ⟩ × ⟨ v ≡ₕ pr u (pr w z) ⟩)
         → ⟨ F4-DRHS a b v ⟩
    step (u , w , z , z∈a , pruw∈b , v≡) =
      ∣ u , ∣ z , ∣ w , (z∈a , (pruw∈b , v≡)) ∣₁ ∣₁ ∣₁

  F4-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F4 a b ⟩ → ⟨ (v ∷ []) ⊨ Φ₄ ⟩
  F4-desc-in v h = F4-sat-in v (F4-mem-DRHS v h)


```

<!--en-->
## F10, one image set
<!--zh-->
## F10，单个像集
<!--/-->

<!--en-->
The image half opens with the slice constructor: a member of `F10 x y`
is a value whose pair with `y` lies in `x`, and the specification states
that equivalence as a path. The defining formula spells the pair
condition out in the object language: some member of `x` reads as the
pair of a set equal to `y` and the candidate itself, which is exactly
what the pair reader's adequacy turns into the path. The equation closes
because a component of a pair in `x` lies in the double union of `x`,
hence in the carrier by transitivity.
<!--zh-->
像的半场以切片构造子开张：`F10 x y` 的成员就是与 `y` 成对后落在 `x` 中的那个值，规格把这条等价陈述为一条道路。定义公式在对象语言中把对条件逐字拼出：`x` 的某个成员读作「与 `y` 相等的集合」和候选自身之对，正是对读式的适足性把它变成道路的那一形状。等式收束靠的是：`x` 中对的一个分量落在 `x` 的二重并内，再经传递性落入载体。
<!--/-->

```agda
module F10Desc (A x y : V ℓ) (x∈ : ⟨ x ∈ˢ A ⟩) (y∈ : ⟨ y ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A)) where
  module PA = AtPr (⟪ A ⟫↪)
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₓ : ⟪ A ⟫
  mₓ = ∈-asFiber {a = x} {b = A} x∈ .fst
  qₓ : ⟪ A ⟫↪ mₓ ≡ x
  qₓ = ∈-asFiber {a = x} {b = A} x∈ .snd
  m_y : ⟪ A ⟫
  m_y = ∈-asFiber {a = y} {b = A} y∈ .fst
  q_y : ⟪ A ⟫↪ m_y ≡ y
  q_y = ∈-asFiber {a = y} {b = A} y∈ .snd

  Φ₁₀ : Formula ⟪ A ⟫ 1
  Φ₁₀ = ∃̇∈ (con mₓ) (∃̇∈ (var zero) (∃̇∈ (var zero)
          (prAt′ f2 f0 f3 ∧̇ (var f0 ≐ con m_y))))

  dΦ₁₀ : Δ₀ Φ₁₀
  dΦ₁₀ = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAt′ f2 f0 f3) δ-≐)))

  F10-sat-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₀ ⟩ → ⟨ pr y v ∈ˢ x ⟩
  F10-sat-out v h = PT.rec (snd (pr y v ∈ˢ x)) (λ { (p , h₁) →
    PT.rec (snd (pr y v ∈ˢ x)) (λ { (w , h₂) →
    PT.rec (snd (pr y v ∈ˢ x)) (λ { (y₀ , h₃) →
      let env = y₀ ∷ w ∷ p ∷ v ∷ []
          p∈x : ⟨ p ∈ˢ x ⟩
          p∈x = subst (λ X → ⟨ p ∈ˢ X ⟩) qₓ (h₁ .fst)
          p≡ : p ≡ pr y₀ v
          p≡ = PA.prAt′-in f2 f0 f3 env (h₃ .snd .fst)
          y₀≡y : y₀ ≡ y
          y₀≡y = subst (λ t → ⟨ y₀ ≡ₕ t ⟩) q_y (h₃ .snd .snd)
          p≡y : pr y v ≡ p
          p≡y = cong₂ (λ a b → pr a b) (sym y₀≡y) refl ∙ sym p≡
      in subst (λ t → ⟨ t ∈ˢ x ⟩) (sym p≡y) p∈x }) (h₂ .snd) }) (h₁ .snd) }) h

  F10-sat-in : (v : V ℓ) → ⟨ pr y v ∈ˢ x ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₀ ⟩
  F10-sat-in v pr∈x = ∣ pr y v , ( subst (λ X → ⟨ pr y v ∈ˢ X ⟩) (sym qₓ) pr∈x
      , ∣ ⁅ y ⁆s , ( ∈∈ₛ {a = ⁅ y ⁆s} {b = pr y v} .snd (singl∈pr y v)
      , ∣ y , ( ∈∈ₛ {a = y} {b = ⁅ y ⁆s} .snd (a∈singl y)
      , ( PA.prAt′-out f2 f0 f3 (y ∷ ⁅ y ⁆s ∷ pr y v ∷ v ∷ []) refl
        , sym q_y ) ) ∣₁ ) ∣₁ ) ∣₁

  F10-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₀ ⟩ → ⟨ v ∈ˢ F10 x y ⟩
  F10-desc-out v h = subst ⟨_⟩ (sym (F10-spec x y v)) (F10-sat-out v h)

  F10-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F10 x y ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₀ ⟩
  F10-desc-in v h = F10-sat-in v (subst ⟨_⟩ (F10-spec x y v) h)

  F10-defSet≡ : DefA.defSet Φ₁₀ ≡ F10 x y
  F10-defSet≡ = extensionality (DefA.defSet Φ₁₀) (F10 x y) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₁₀ ⊆ F10 x y ⟩
    sub₁ y' y'∈ₛ = PT.rec (snd (y' ∈ₛ F10 x y)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y'} {b = DefA.defSet Φ₁₀} .snd y'∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₁₀ m ⟩ → ⟪ A ⟫↪ m ≡ y'
          → ⟨ y' ∈ₛ F10 x y ⟩
      go m s q = subst (λ w → ⟨ w ∈ₛ F10 x y ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F10 x y} .fst
          (F10-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₁₀ dΦ₁₀ m) ∣ (m , s) , refl ∣₁)))
    sub₂ : ⟨ F10 x y ⊆ DefA.defSet Φ₁₀ ⟩
    sub₂ y' y'∈ₛ = go (∈∈ₛ {a = y'} {b = F10 x y} .snd y'∈ₛ)
      where
      go : ⟨ y' ∈ˢ F10 x y ⟩ → ⟨ y' ∈ₛ DefA.defSet Φ₁₀ ⟩
      go h = let
          pr∈x : ⟨ pr y y' ∈ˢ x ⟩
          pr∈x = subst ⟨_⟩ (F10-spec x y y') h
          y'∈A : ⟨ y' ∈ˢ A ⟩
          y'∈A = ⋃⋃-in-A A x x∈ Atrans y' (prR-in-⋃⋃ x y y' pr∈x)
          fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y')
          fib = ∈-asFiber {a = y'} {b = A} y'∈A
          m : ⟪ A ⟫
          m = fib .fst
          q : ⟪ A ⟫↪ m ≡ y'
          q = fib .snd
          in subst (λ z → ⟨ z ∈ₛ DefA.defSet Φ₁₀ ⟩) q
            (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ₁₀} .fst
              (subst ⟨_⟩ (sym (Ch.chain Φ₁₀ dΦ₁₀ m))
                (F10-desc-in (⟪ A ⟫↪ m)
                  (subst (λ z → ⟨ z ∈ˢ F10 x y ⟩) (sym q) h))))
```

<!--en-->
## F8, the collection of slices
<!--zh-->
## F8，切片之集
<!--/-->

<!--en-->
F8 collects one slice per member of its second argument, and the
description formula reads the slice equality extensionally: a candidate
`w` equals the slice at `z` exactly when membership in `w` matches the
pair condition `pr z v ∈ x` on both sides. The first inclusion binds the
member `v` of `w` and reads the pair from `x`; the second reads the pair
out of `x` through its waypoints and forces the candidate's membership.
The two directions of the adequacy compose with the specification's
small-index form through the fibre of `z` in `y`.
<!--zh-->
F8 为其第二实参的每个成员收拢一个切片，定义公式外延地读切片等式：候选 `w` 等于 `z` 处的切片，恰在「`w` 的成员关系」与「对条件 `pr z v ∈ x`」在两边相符之时。第一包含读 `w` 的成员 `v`，从 `x` 中读出对；第二包含从 `x` 中经中转站读出对，逼出候选中的成员。适足的两个方向经 `z` 在 `y` 中的纤维与规格的小索引形式合成。
<!--/-->

```agda
module F8Desc (A x y : V ℓ) (x∈ : ⟨ x ∈ˢ A ⟩) (y∈ : ⟨ y ∈ˢ A ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A)) where
  module PA = AtPr (⟪ A ⟫↪)
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_; ⟦_⟧ )

  mₓ : ⟪ A ⟫
  mₓ = ∈-asFiber {a = x} {b = A} x∈ .fst
  qₓ : ⟪ A ⟫↪ mₓ ≡ x
  qₓ = ∈-asFiber {a = x} {b = A} x∈ .snd
  m_y : ⟪ A ⟫
  m_y = ∈-asFiber {a = y} {b = A} y∈ .fst
  q_y : ⟪ A ⟫↪ m_y ≡ y
  q_y = ∈-asFiber {a = y} {b = A} y∈ .snd

  sliceBody : Formula ⟪ A ⟫ 2
  sliceBody = ∀̇∈ (var f1) ((var zero ∈̇ var f2) ⇒̇ (∃̇∈ (con mₓ) (prAt′ f0 f2 f1)))
          ∧̇ (∀̇∈ (con mₓ) (∀̇∈ (var zero) (∀̇∈ (var zero)
               (prAt′ f2 f3 f0 ⇒̇ (var zero ∈̇ var f4)))))

  Φ₈ : Formula ⟪ A ⟫ 1
  Φ₈ = ∃̇∈ (con m_y) sliceBody

  dΦ₈ : Δ₀ Φ₈
  dΦ₈ = δ-∃∈ (δ-∧ (δ-∀∈ (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-prAt′ f0 f2 f1))))
                  (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAt′ f2 f3 f0) δ-∈)))))

  F8-sat-out : (w : V ℓ) → ⟨ (w ∷ []) ⊨ Φ₈ ⟩
             → ∥ Σ[ z ∈ V ℓ ] ⟨ z ∈ˢ y ⟩ × ⟨ w ⊆ F10 x z ⟩ × ⟨ F10 x z ⊆ w ⟩ ∥₁
  F8-sat-out w h = PT.rec PT.squash₁ step h
    where
    tgt : Type (ℓ-suc ℓ)
    tgt = Σ[ z ∈ V ℓ ] ⟨ z ∈ˢ y ⟩ × ⟨ w ⊆ F10 x z ⟩ × ⟨ F10 x z ⊆ w ⟩
    step : Σ[ z ∈ V ℓ ] ⟨ (z ∈ˢ ⟪ A ⟫↪ m_y) ⊓ ((z ∷ w ∷ []) ⊨ sliceBody) ⟩
         → ∥ tgt ∥₁
    step (z , h₁) = ∣ z , ( subst (λ X → ⟨ z ∈ˢ X ⟩) q_y (h₁ .fst)
                          , inc1 , inc2 ) ∣₁
      where
      inc1 : ⟨ w ⊆ F10 x z ⟩
      inc1 v v∈ₛw = ∈∈ₛ {a = v} {b = F10 x z} .fst
        (subst ⟨_⟩ (sym (F10-spec x z v)) pr∈x)
        where
        pr∈x : ⟨ pr z v ∈ˢ x ⟩
        pr∈x = PT.rec (snd (pr z v ∈ˢ x)) (λ { (p , h₂) →
          subst (λ t → ⟨ t ∈ˢ x ⟩) (PA.prAt′-in f0 f2 f1 (p ∷ v ∷ z ∷ w ∷ []) (h₂ .snd))
            (subst (λ X → ⟨ p ∈ˢ X ⟩) qₓ (h₂ .fst)) })
          (h₁ .snd .fst v (∈∈ₛ {a = v} {b = w} .snd v∈ₛw)
             (∈∈ₛ {a = v} {b = w} .snd v∈ₛw))
      inc2 : ⟨ F10 x z ⊆ w ⟩
      inc2 v v∈ₛF = ∈∈ₛ {a = v} {b = w} .fst v∈w
        where
        pr∈x : ⟨ pr z v ∈ˢ x ⟩
        pr∈x = subst ⟨_⟩ (F10-spec x z v) (∈∈ₛ {a = v} {b = F10 x z} .snd v∈ₛF)
        v∈w : ⟨ v ∈ˢ w ⟩
        v∈w = h₁ .snd .snd (pr z v) (subst (λ X → ⟨ pr z v ∈ˢ X ⟩) (sym qₓ) pr∈x)
          (⁅ z , v ⁆) (∈∈ₛ {a = ⁅ z , v ⁆} {b = pr z v} .snd (pair∈pr z v))
          v (∈∈ₛ {a = v} {b = ⁅ z , v ⁆} .snd (v∈pair z v))
          (PA.prAt′-out f2 f3 f0 (v ∷ ⁅ z , v ⁆ ∷ pr z v ∷ z ∷ w ∷ []) refl)

  F8-sat-in : (w z : V ℓ) → ⟨ z ∈ˢ y ⟩
            → ⟨ w ⊆ F10 x z ⟩ → ⟨ F10 x z ⊆ w ⟩ → ⟨ (w ∷ []) ⊨ Φ₈ ⟩
  F8-sat-in w z z∈y inc1 inc2 =
    ∣ z , ( subst (λ X → ⟨ z ∈ˢ X ⟩) (sym q_y) z∈y
          , ( ∀₁ , ∀₂ ) ) ∣₁
    where
    ∀₁ : (v : V ℓ) → ⟨ v ∈ˢ w ⟩
        → ⟨ (v ∷ z ∷ w ∷ []) ⊨ ((var zero ∈̇ var f2) ⇒̇ (∃̇∈ (con mₓ) (prAt′ f0 f2 f1))) ⟩
    ∀₁ v v∈w = λ _ → ∣ pr z v
      , ( subst (λ X → ⟨ pr z v ∈ˢ X ⟩) (sym qₓ) pr∈x
        , PA.prAt′-out f0 f2 f1 (pr z v ∷ v ∷ z ∷ w ∷ []) refl ) ∣₁
      where
      pr∈x : ⟨ pr z v ∈ˢ x ⟩
      pr∈x = subst ⟨_⟩ (F10-spec x z v) (∈∈ₛ {a = v} {b = F10 x z} .snd (inc1 v (∈∈ₛ {a = v} {b = w} .fst v∈w)))
    ∀₂ : (p : V ℓ) → ⟨ p ∈ˢ ⟪ A ⟫↪ mₓ ⟩ → (w' : V ℓ) → ⟨ w' ∈ˢ p ⟩
       → (v : V ℓ) → ⟨ v ∈ˢ w' ⟩
       → ⟨ (v ∷ w' ∷ p ∷ z ∷ w ∷ []) ⊨ (prAt′ f2 f3 f0 ⇒̇ (var zero ∈̇ var f4)) ⟩
    ∀₂ p p∈x w' w'∈p v v∈w' satpr = v∈w
      where
      p≡ : p ≡ pr z v
      p≡ = PA.prAt′-in f2 f3 f0 (v ∷ w' ∷ p ∷ z ∷ w ∷ []) satpr
      v∈w : ⟨ v ∈ˢ w ⟩
      v∈w = ∈∈ₛ {a = v} {b = w} .snd
        (inc2 v (∈∈ₛ {a = v} {b = F10 x z} .fst
          (subst ⟨_⟩ (sym (F10-spec x z v))
            (subst (λ t → ⟨ t ∈ˢ x ⟩) p≡
              (subst (λ X → ⟨ p ∈ˢ X ⟩) qₓ p∈x)))))

  F8-desc-out : (w : V ℓ) → ⟨ (w ∷ []) ⊨ Φ₈ ⟩ → ⟨ w ∈ˢ F8 x y ⟩
  F8-desc-out w h = PT.rec (snd (w ∈ˢ F8 x y)) go (F8-sat-out w h)
    where
    go : Σ[ z ∈ V ℓ ] ⟨ z ∈ˢ y ⟩ × ⟨ w ⊆ F10 x z ⟩ × ⟨ F10 x z ⊆ w ⟩
       → ⟨ w ∈ˢ F8 x y ⟩
    go (z , z∈y , inc1 , inc2) = subst ⟨_⟩ (sym (F8-spec x y w))
      (∣ m , (cong (F10 x) q ∙ sym w≡) ∣₁)
      where
      w≡ : w ≡ F10 x z
      w≡ = extensionality w (F10 x z) (inc1 , inc2)
      m : ⟪ y ⟫
      m = ∈-asFiber {a = z} {b = y} z∈y .fst
      q : ⟪ y ⟫↪ m ≡ z
      q = ∈-asFiber {a = z} {b = y} z∈y .snd

  F8-desc-in : (w : V ℓ) → ⟨ w ∈ˢ F8 x y ⟩ → ⟨ (w ∷ []) ⊨ Φ₈ ⟩
  F8-desc-in w h = PT.rec (snd ((w ∷ []) ⊨ Φ₈)) go
    (subst ⟨_⟩ (F8-spec x y w) h)
    where
    go : Σ[ m ∈ ⟪ y ⟫ ] ⟨ F10 x (⟪ y ⟫↪ m) ≡ₕ w ⟩ → ⟨ (w ∷ []) ⊨ Φ₈ ⟩
    go (m , q) = F8-sat-in w (⟪ y ⟫↪ m) z∈y′ inc1 inc2
      where
      z : V ℓ
      z = ⟪ y ⟫↪ m
      z∈y′ : ⟨ z ∈ˢ y ⟩
      z∈y′ = ∈∈ₛ {a = z} {b = y} .snd (∈ₛ⟪ y ⟫↪ m)
      inc1 : ⟨ w ⊆ F10 x z ⟩
      inc1 v v∈ₛw = ∈∈ₛ {a = v} {b = F10 x z} .fst
        (subst (λ t → ⟨ v ∈ˢ t ⟩) (sym q) (∈∈ₛ {a = v} {b = w} .snd v∈ₛw))
      inc2 : ⟨ F10 x z ⊆ w ⟩
      inc2 v v∈ₛF = ∈∈ₛ {a = v} {b = w} .fst
        (subst (λ t → ⟨ v ∈ˢ t ⟩) q (∈∈ₛ {a = v} {b = F10 x z} .snd v∈ₛF))

  F8-defSet≡ : (cl : ⟨ F8 x y ⊆ A ⟩) → DefA.defSet Φ₈ ≡ F8 x y
  F8-defSet≡ cl = extensionality (DefA.defSet Φ₈) (F8 x y) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ₈ ⊆ F8 x y ⟩
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ F8 x y)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = w} {b = DefA.defSet Φ₈} .snd w∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ₈ m ⟩ → ⟪ A ⟫↪ m ≡ w
          → ⟨ w ∈ₛ F8 x y ⟩
      go m s q = subst (λ t → ⟨ t ∈ₛ F8 x y ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = F8 x y} .fst
          (F8-desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₈ dΦ₈ m) ∣ (m , s) , refl ∣₁)))
    sub₂ : ⟨ F8 x y ⊆ DefA.defSet Φ₈ ⟩
    sub₂ w w∈ₛ = let
        w∈A : ⟨ w ∈ˢ A ⟩
        w∈A = ∈∈ₛ {a = w} {b = A} .snd (cl w w∈ₛ)
        fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ w)
        fib = ∈-asFiber {a = w} {b = A} w∈A
        m : ⟪ A ⟫
        m = fib .fst
        q : ⟪ A ⟫↪ m ≡ w
        q = fib .snd
        in subst (λ t → ⟨ t ∈ₛ DefA.defSet Φ₈ ⟩) q
          (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ₈} .fst
            (subst ⟨_⟩ (sym (Ch.chain Φ₈ dΦ₈ m))
              (F8-desc-in (⟪ A ⟫↪ m)
                (subst (λ t → ⟨ t ∈ˢ F8 x y ⟩) (sym q)
                  (∈∈ₛ {a = w} {b = F8 x y} .snd w∈ₛ)))))
```

<!--en-->
## F11 to F14, one pair-value frame
<!--zh-->
## F11 至 F14，一个对值框架
<!--/-->

<!--en-->
The four tuple operations are all pair-shaped values: with the pair
decomposition `y ≡ pr a b` in hand, each image is the unordered pair of
two named members, either `{a}` and `{a, c}` when the operation builds a
right-nested triple, or `a` and `c` when it builds the flat unordered
pair, where `c` is `pr x b` or `pr b x` according to the coordinate. One
frame therefore carries all four: the two members as parameters with
their carrier memberships, the value equation back to their unordered
pair, and the adequacy and the definable-subset equation read off the
pair specification. Each instantiation names only the coordinates.
<!--zh-->
四个三元组运算都是对形值：拿到对分解 `y ≡ pr a b` 后，每个像都是两个指名成员的无序对，造右嵌套三元组时是 `{a}` 与 `{a, c}`，造平铺无序对时是 `a` 与 `c`，其中 `c` 依坐标是 `pr x b` 或 `pr b x`。一个框架因此承载全部四个：两个成员连同其载体隶属作参数，值等式回到它们的无序对，适足与可定义子集等式从对规格读出。每个实例只点名坐标。
<!--/-->

```agda
module PairValFrame (A : V ℓ) (val m₁ m₂ : V ℓ)
  (m₁∈ : ⟨ m₁ ∈ˢ A ⟩) (m₂∈ : ⟨ m₂ ∈ˢ A ⟩) (val≡ : val ≡ F0 m₁ m₂)
  (Atrans : Transitive 𝒮ᵥ (λ x → x ∈ˢ A)) where
  module Fr = F0F9Frame A m₁ m₂ m₁∈ m₂∈
  module DefA = DefOf A
  module Ch = Chain A Atrans
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )

  Φ : Formula ⟪ A ⟫ 1
  Φ = Fr.Φ

  dΦ : Δ₀ Φ
  dΦ = Fr.dΦ

  desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ ⟩ → ⟨ v ∈ˢ val ⟩
  desc-out v h = subst (λ s → ⟨ v ∈ˢ s ⟩) (sym val≡)
    (F0-spec m₁ m₂ v .snd (Fr.eq-out v h))

  desc-in : (v : V ℓ) → ⟨ v ∈ˢ val ⟩ → ⟨ (v ∷ []) ⊨ Φ ⟩
  desc-in v h = Fr.eq-in v
    (F0-spec m₁ m₂ v .fst (subst (λ s → ⟨ v ∈ˢ s ⟩) val≡ h))

  defSet≡ : DefA.defSet Φ ≡ val
  defSet≡ = extensionality (DefA.defSet Φ) val (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet Φ ⊆ val ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ val)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
      where
      go : (m : ⟪ A ⟫) → ⟨ DefA.smallSat Φ m ⟩ → ⟪ A ⟫↪ m ≡ y
          → ⟨ y ∈ₛ val ⟩
      go m s q = subst (λ t → ⟨ t ∈ₛ val ⟩) q
        (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = val} .fst
          (desc-out (⟪ A ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ dΦ m) ∣ (m , s) , refl ∣₁)))
    sub₂ : ⟨ val ⊆ DefA.defSet Φ ⟩
    sub₂ y y∈ₛ = go (F0-spec m₁ m₂ y .fst
      (subst (λ t → ⟨ y ∈ˢ t ⟩) val≡ (∈∈ₛ {a = y} {b = val} .snd y∈ₛ)))
      where
      go : ⟨ (y ≡ₕ m₁) ⊔ (y ≡ₕ m₂) ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
      go h = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) step h
        where
        step : ⟨ y ≡ₕ m₁ ⟩ ⊎ ⟨ y ≡ₕ m₂ ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
        step (inl y≡m₁) = let
            y∈A : ⟨ y ∈ˢ A ⟩
            y∈A = subst (λ t → ⟨ t ∈ˢ A ⟩) (sym y≡m₁) m₁∈
            fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
            fib = ∈-asFiber {a = y} {b = A} y∈A
            m : ⟪ A ⟫
            m = fib .fst
            q : ⟪ A ⟫↪ m ≡ y
            q = fib .snd
            in subst (λ t → ⟨ t ∈ₛ DefA.defSet Φ ⟩) q
              (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (Ch.chain Φ dΦ m))
                  (desc-in (⟪ A ⟫↪ m)
                    (subst (λ t → ⟨ t ∈ˢ val ⟩) (sym q)
                      (subst (λ t → ⟨ t ∈ˢ val ⟩) (sym y≡m₁)
                        (subst (λ t → ⟨ m₁ ∈ˢ t ⟩) (sym val≡)
                          (F0-spec m₁ m₂ m₁ .snd ∣ inl refl ∣₁)))))))
        step (inr y≡m₂) = let
            y∈A : ⟨ y ∈ˢ A ⟩
            y∈A = subst (λ t → ⟨ t ∈ˢ A ⟩) (sym y≡m₂) m₂∈
            fib : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ y)
            fib = ∈-asFiber {a = y} {b = A} y∈A
            m : ⟪ A ⟫
            m = fib .fst
            q : ⟪ A ⟫↪ m ≡ y
            q = fib .snd
            in subst (λ t → ⟨ t ∈ₛ DefA.defSet Φ ⟩) q
              (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (Ch.chain Φ dΦ m))
                  (desc-in (⟪ A ⟫↪ m)
                    (subst (λ t → ⟨ t ∈ˢ val ⟩) (sym q)
                      (subst (λ t → ⟨ t ∈ˢ val ⟩) (sym y≡m₂)
                        (subst (λ t → ⟨ m₂ ∈ˢ t ⟩) (sym val≡)
                          (F0-spec m₁ m₂ m₂ .snd ∣ inr refl ∣₁)))))))
```

<!--en-->
The four instantiations differ only in the coordinates. F11 and F12 read
their middle member out of the triple shape, F13 and F14 out of the flat
pair; each names the frame's formula, witness, adequacy directions, and
definable-subset equation under its own F-name.
<!--zh-->
四个实例只差坐标。F11 与 F12 从三元组形状中读出中间成员，F13 与 F14 从平铺对中读出；每个都把框架的公式、见证、适足方向与可定义子集等式以自家 F 名点出。
<!--/-->

```agda
module F11Desc (A x a b : V ℓ)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A))
  (c₁∈ : ⟨ ⁅ a ⁆s ∈ˢ A ⟩) (c₂∈ : ⟨ ⁅ a , pr x b ⁆ ∈ˢ A ⟩)
  (y : V ℓ) (y≡ : y ≡ pr a b) where
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )
  module DefA = DefOf A
  open PairValFrame A (F11 x y) ⁅ a ⁆s ⁅ a , pr x b ⁆ c₁∈ c₂∈
    (F11-spec x y a b y≡) Atrans
    using ( Φ; dΦ; desc-out; desc-in; defSet≡ )

  Φ₁₁ : Formula ⟪ A ⟫ 1
  Φ₁₁ = Φ

  dΦ₁₁ : Δ₀ Φ₁₁
  dΦ₁₁ = dΦ

  F11-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₁ ⟩ → ⟨ v ∈ˢ F11 x y ⟩
  F11-desc-out = desc-out

  F11-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F11 x y ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₁ ⟩
  F11-desc-in = desc-in

  F11-defSet≡ : DefA.defSet Φ₁₁ ≡ F11 x y
  F11-defSet≡ = defSet≡

module F12Desc (A x a b : V ℓ)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A))
  (c₁∈ : ⟨ ⁅ a ⁆s ∈ˢ A ⟩) (c₂∈ : ⟨ ⁅ a , pr b x ⁆ ∈ˢ A ⟩)
  (y : V ℓ) (y≡ : y ≡ pr a b) where
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )
  module DefA = DefOf A
  open PairValFrame A (F12 x y) ⁅ a ⁆s ⁅ a , pr b x ⁆ c₁∈ c₂∈
    (F12-spec x y a b y≡) Atrans
    using ( Φ; dΦ; desc-out; desc-in; defSet≡ )

  Φ₁₂ : Formula ⟪ A ⟫ 1
  Φ₁₂ = Φ

  dΦ₁₂ : Δ₀ Φ₁₂
  dΦ₁₂ = dΦ

  F12-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₂ ⟩ → ⟨ v ∈ˢ F12 x y ⟩
  F12-desc-out = desc-out

  F12-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F12 x y ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₂ ⟩
  F12-desc-in = desc-in

  F12-defSet≡ : DefA.defSet Φ₁₂ ≡ F12 x y
  F12-defSet≡ = defSet≡

module F13Desc (A x a b : V ℓ)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A))
  (a∈ : ⟨ a ∈ˢ A ⟩) (c∈ : ⟨ pr b x ∈ˢ A ⟩)
  (y : V ℓ) (y≡ : y ≡ pr a b) where
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )
  module DefA = DefOf A
  open PairValFrame A (F13 x y) a (pr b x) a∈ c∈
    (F13-spec x y a b y≡) Atrans
    using ( Φ; dΦ; desc-out; desc-in; defSet≡ )

  Φ₁₃ : Formula ⟪ A ⟫ 1
  Φ₁₃ = Φ

  dΦ₁₃ : Δ₀ Φ₁₃
  dΦ₁₃ = dΦ

  F13-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₃ ⟩ → ⟨ v ∈ˢ F13 x y ⟩
  F13-desc-out = desc-out

  F13-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F13 x y ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₃ ⟩
  F13-desc-in = desc-in

  F13-defSet≡ : DefA.defSet Φ₁₃ ≡ F13 x y
  F13-defSet≡ = defSet≡

module F14Desc (A x a b : V ℓ)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ A))
  (a∈ : ⟨ a ∈ˢ A ⟩) (c∈ : ⟨ pr x b ∈ˢ A ⟩)
  (y : V ℓ) (y≡ : y ≡ pr a b) where
  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemA.At (⟪ A ⟫) (⟪ A ⟫↪) using ( _⊨_ )
  module DefA = DefOf A
  open PairValFrame A (F14 x y) a (pr x b) a∈ c∈
    (F14-spec x y a b y≡) Atrans
    using ( Φ; dΦ; desc-out; desc-in; defSet≡ )

  Φ₁₄ : Formula ⟪ A ⟫ 1
  Φ₁₄ = Φ

  dΦ₁₄ : Δ₀ Φ₁₄
  dΦ₁₄ = dΦ

  F14-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₄ ⟩ → ⟨ v ∈ˢ F14 x y ⟩
  F14-desc-out = desc-out

  F14-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F14 x y ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₄ ⟩
  F14-desc-in = desc-in

  F14-defSet≡ : DefA.defSet Φ₁₄ ≡ F14 x y
  F14-defSet≡ = defSet≡
```

<!--en-->
## F15, the relativization slot
<!--zh-->
## F15，相对化槽
<!--/-->

<!--en-->
The relativized basis adds one predicate slot, and the description of
the cut `F15 P x` is the two membership atoms joined by the object
conjunction. The predicate set enters the formula as an ordinary member
of the carrier, so the description instantiates the images chapter's
parameterized module at the slot `P`; both memberships deliver the
carrier membership of the candidate, and the equation closes with no
transitivity beyond what the chain consumes.
<!--zh-->
相对化基增加一个谓词槽，截断 `F15 P x` 的描述是对象合取联起的两条隶属原子。谓词集作为载体的普通成员进公式，故描述在槽 `P` 处实例化像章的参数化模块；两条隶属都直接交出候选的载体隶属，等式除链所消费者外不再需要传递性。
<!--/-->

```agda
module F15Desc (U P x : V ℓ) (P∈ : ⟨ P ∈ˢ U ⟩) (x∈ : ⟨ x ∈ˢ U ⟩)
  (Atrans : Transitive 𝒮ᵥ (λ z → z ∈ˢ U)) where
  module F15P = F15Of P
  module DefU = DefOf U
  module Ch = Chain U Atrans
  module SemU = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open SemU.At (⟪ U ⟫) (⟪ U ⟫↪) using ( _⊨_ )

  mₚ : ⟪ U ⟫
  mₚ = ∈-asFiber {a = P} {b = U} P∈ .fst
  qₚ : ⟪ U ⟫↪ mₚ ≡ P
  qₚ = ∈-asFiber {a = P} {b = U} P∈ .snd
  mₓ : ⟪ U ⟫
  mₓ = ∈-asFiber {a = x} {b = U} x∈ .fst
  qₓ : ⟪ U ⟫↪ mₓ ≡ x
  qₓ = ∈-asFiber {a = x} {b = U} x∈ .snd

  Φ₁₅ : Formula ⟪ U ⟫ 1
  Φ₁₅ = (var zero ∈̇ con mₓ) ∧̇ (var zero ∈̇ con mₚ)

  dΦ₁₅ : Δ₀ Φ₁₅
  dΦ₁₅ = δ-∧ δ-∈ δ-∈

  F15-desc-out : (v : V ℓ) → ⟨ (v ∷ []) ⊨ Φ₁₅ ⟩ → ⟨ v ∈ˢ F15P.F15 x ⟩
  F15-desc-out v h = subst ⟨_⟩ (sym (F15P.F15-spec x v)) (v∈x , v∈P)
    where
    v∈x : ⟨ v ∈ˢ x ⟩
    v∈x = subst (λ X → ⟨ v ∈ˢ X ⟩) qₓ (h .fst)
    v∈P : ⟨ v ∈ˢ P ⟩
    v∈P = subst (λ X → ⟨ v ∈ˢ X ⟩) qₚ (h .snd)

  F15-desc-in : (v : V ℓ) → ⟨ v ∈ˢ F15P.F15 x ⟩ → ⟨ (v ∷ []) ⊨ Φ₁₅ ⟩
  F15-desc-in v h = let h' = subst ⟨_⟩ (F15P.F15-spec x v) h
    in ( subst (λ X → ⟨ v ∈ˢ X ⟩) (sym qₓ) (h' .fst)
       , subst (λ X → ⟨ v ∈ˢ X ⟩) (sym qₚ) (h' .snd) )

  F15-defSet≡ : DefU.defSet Φ₁₅ ≡ F15P.F15 x
  F15-defSet≡ = extensionality (DefU.defSet Φ₁₅) (F15P.F15 x) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefU.defSet Φ₁₅ ⊆ F15P.F15 x ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ F15P.F15 x)) (λ { ((m , s) , q) → go m s q })
      (∈∈ₛ {a = y} {b = DefU.defSet Φ₁₅} .snd y∈ₛ)
      where
      go : (m : ⟪ U ⟫) → ⟨ DefU.smallSat Φ₁₅ m ⟩ → ⟪ U ⟫↪ m ≡ y
          → ⟨ y ∈ₛ F15P.F15 x ⟩
      go m s q = subst (λ t → ⟨ t ∈ₛ F15P.F15 x ⟩) q
        (∈∈ₛ {a = ⟪ U ⟫↪ m} {b = F15P.F15 x} .fst
          (F15-desc-out (⟪ U ⟫↪ m)
            (subst ⟨_⟩ (Ch.chain Φ₁₅ dΦ₁₅ m) ∣ (m , s) , refl ∣₁)))
    sub₂ : ⟨ F15P.F15 x ⊆ DefU.defSet Φ₁₅ ⟩
    sub₂ y y∈ₛ = let
        y∈P : ⟨ y ∈ˢ P ⟩
        y∈P = subst ⟨_⟩ (F15P.F15-spec x y)
          (∈∈ₛ {a = y} {b = F15P.F15 x} .snd y∈ₛ) .snd
        y∈U : ⟨ y ∈ˢ U ⟩
        y∈U = Atrans {x = P} {y = y} y∈P P∈
        fib : Σ[ m ∈ ⟪ U ⟫ ] (⟪ U ⟫↪ m ≡ y)
        fib = ∈-asFiber {a = y} {b = U} y∈U
        m : ⟪ U ⟫
        m = fib .fst
        q : ⟪ U ⟫↪ m ≡ y
        q = fib .snd
        in subst (λ t → ⟨ t ∈ₛ DefU.defSet Φ₁₅ ⟩) q
          (∈∈ₛ {a = ⟪ U ⟫↪ m} {b = DefU.defSet Φ₁₅} .fst
            (subst ⟨_⟩ (sym (Ch.chain Φ₁₅ dΦ₁₅ m))
              (F15-desc-in (⟪ U ⟫↪ m)
                (subst (λ t → ⟨ t ∈ˢ F15P.F15 x ⟩) (sym q)
                  (∈∈ₛ {a = y} {b = F15P.F15 x} .snd y∈ₛ)))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Sixteen defining formulas and their Delta-0 witnesses are in place, one per
committed operation, and each carries the two adequacy directions against
its image. F0, F1, F5, F9, F10, and F15 close with the definable-subset
equation outright, and the pair-value frame closes F11 to F14 under the
switch-supplied member hypotheses; F8's equation closes under the slice
closure hypothesis. F2, F3, F4, F6, and F7 close the membership-to-shape
direction through the operations chapter's read lemmas, and their
definable-subset equations are walled by the seal on the specification's
right-hand side, recorded per operation in the batch report. The carrier is
a module parameter throughout, and nothing of the operations ever unfolds.
<!--zh-->
十六条定义公式与十六个 Δ₀ 见证就位，十六条承诺运算各一条，每条都带对像的两个适足方向。F0、F1、F5、F9、F10、F15 以可定义子集等式直接收束，对值框架在切换章供应的成员假设下收束 F11 至 F14；F8 的等式在切片闭包假设下收束。F2、F3、F4、F6、F7 经运算章的读引理收束从隶属到像形的方向，其可定义子集等式仍被规格右端的封印挡着，逐条记入批次报告。载体自始至终是模块参数，运算本身从不展开。
<!--/-->
