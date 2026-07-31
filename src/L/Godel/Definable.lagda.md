# The operations, described

<!--en-->
Each operation of the previous chapter, said in the object language. For an
operation and a slot, the description is one extension formula: the slot holds
exactly the members the operation admits. What this chapter proves about each
description is an **identity**: an environment satisfies it precisely when the
set at the slot is the operation applied to the sets at the argument slots, on
the nose, by extensionality. The internal recursions to come will bind these
descriptions inside their graphs, and an identity is what lets a bound slot be
traded for the operation itself without a residue.

One frame carries all of them. A description of this shape is an
`extAt`{.Agda} over a body, and its two readings are always the same four
moves: open the extension, convert the body's satisfaction to a membership,
carry the binder's constructibility across, and close with extensionality. The
frame takes the body, the target set, and the two conversions, and returns
both readings; each operation then costs its body and its conversions, which
are the only parts that differ.
<!--zh-->
每个上一章的运算，用对象语言说出。给定运算与一个槽位，描述是一条外延公式：该槽位所持有的恰是运算所接纳的诸成员。本章对每条描述证明的是一条**等同**：一个环境满足它，当且仅当槽位处的集合就是运算施于诸实参槽位处集合的结果，不多不少，由外延性钉死。即将到来的内部递归会把这些描述绑进自己的图里，而等同正是使一个被绑定的槽位能够无残余地换成运算本身的东西。

一个框架承载全部。这种形状的描述是罩着一个体的 `extAt`{.Agda}，而它的两条读式永远是同样四步：打开外延、把体的满足转换为一次隶属、把束缚元的可构造性搬过去、以外延性收口。框架收下体、目标集与两个转换，交回两条读式；于是每个运算只花它的体与它的转换，而那正是彼此相异的全部。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Godel.Definable {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; extAt-in-both
        ; prʟ; prʟ-fst; prAtL; prAtL-adequate )
open import L.Godel.Operations {ℓ}
  using ( _∪_; ∪-left; ∪-right; ∪-out; _∖_; ∖-in; ∖-out
        ; product; product-in; product-out
        ; memberGraph; memberGraph-in; memberGraph-out )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; _⊆_; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The frame

The description sits at slot `k`; the body `Φ`{.Agda} speaks about the bound
member under one extra binder; the target `F`{.Agda} is the set the
description means. Three conversions parameterize the frame: the body's
satisfaction read as membership in the target, filled back from it, and the
constructibility of any member of the target, which is what lets a bare set be
packaged as a binder. Both readings quantify over nothing but the
environment: the identity is between the set at the slot and the target.
<!--zh-->
## 框架

描述坐在槽位 `k` 处；体 `Φ`{.Agda} 在多出的一个束缚元下谈论被绑定的成员；目标 `F`{.Agda} 是描述所意指的集合。框架由三个转换参数化：体的满足读作目标中的隶属、再从后者填回，以及目标任意成员的可构造性，正是它使一个裸集合能被打包成束缚元。两条读式除环境外不量化任何东西：等同发生在槽位处的集合与目标之间。
<!--/-->

```agda
module Describes {n : ℕ} (k : Fin n) (Φ : Formula S (suc n)) (γ : S ^ n)
  (F : V ℓ)
  (memL : (y : V ℓ) → ⟨ y ∈ F ⟩ → ⟨ isL y ⟩)
  (read : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ F ⟩)
  (fill : (z : S) → ⟨ fst z ∈ F ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩)
  where

  private
    K : V ℓ
    K = fst (lookup k γ)

  describes-out : ⟨ γ ⊨ extAt k Φ ⟩ → fst (lookup k γ) ≡ F
  describes-out h = extensionality K F (sub₁ , sub₂)
    where
    sub₁ : ⟨ K ⊆ F ⟩
    sub₁ y y∈ₛK = ∈∈ₛ {a = y} {b = F} .fst (read z (extAt-out k Φ γ h z y∈K))
      where
      y∈K : ⟨ y ∈ K ⟩
      y∈K = ∈∈ₛ {a = y} {b = K} .snd y∈ₛK
      z : S
      z = y , isL-trans {x = K} {y = y} y∈K (lookup k γ .snd)
    sub₂ : ⟨ F ⊆ K ⟩
    sub₂ y y∈ₛF = ∈∈ₛ {a = y} {b = K} .fst (extAt-in k Φ γ h z (fill z y∈F))
      where
      y∈F : ⟨ y ∈ F ⟩
      y∈F = ∈∈ₛ {a = y} {b = F} .snd y∈ₛF
      z : S
      z = y , memL y y∈F

  describes-in : fst (lookup k γ) ≡ F → ⟨ γ ⊨ extAt k Φ ⟩
  describes-in e = extAt-in-both k Φ γ
    (λ z z∈K → fill z (subst (λ X → ⟨ fst z ∈ X ⟩) e z∈K))
    (λ z hz → subst (λ X → ⟨ fst z ∈ X ⟩) (sym e) (read z hz))
```

<!--en-->
## Difference and union

The Boolean pair, and the two cheapest bodies: atoms under a conjunction with
a negation, and atoms under a disjunction. The negation of the object language
reads back as the refutation the difference operation carries in its fiber,
and the disjunction as the sum the union indexes over, so each conversion is
one law of the previous chapter and nothing else. The constructibility of a
member goes through the argument slot that holds it.
<!--zh-->
## 差与并

布尔那一对，与两个最便宜的体：合取带否定之下的原子，与析取之下的原子。对象语言的否定读回去就是差运算在纤维里携带的那个反驳，析取读回去就是并所索引的那个和，故每个转换恰是上一章的一条定律，别无其他。成员的可构造性经持有它的那个实参槽位过去。
<!--/-->

```agda
diffAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
diffAt k i j =
  extAt k ((var zero ∈̇ var (suc i)) ∧̇ (¬̇ (var zero ∈̇ var (suc j))))

module _ {n : ℕ} (k i j : Fin n) (γ : S ^ n) where
  private
    Φ : Formula S (suc n)
    Φ = (var zero ∈̇ var (suc i)) ∧̇ (¬̇ (var zero ∈̇ var (suc j)))

    A B : V ℓ
    A = fst (lookup i γ)
    B = fst (lookup j γ)

    module D = Describes k Φ γ (A ∖ B)
      (λ y y∈d → isL-trans {x = A} {y = y}
          (∖-out {X = A} {Y = B} {x = y} y∈d .fst) (lookup i γ .snd))
      (λ z hz → ∖-in {X = A} {Y = B} {x = fst z} (hz .fst) (hz .snd))
      (λ z z∈d → ∖-out {X = A} {Y = B} {x = fst z} z∈d)

  diffAt-out : ⟨ γ ⊨ diffAt k i j ⟩
             → fst (lookup k γ) ≡ fst (lookup i γ) ∖ fst (lookup j γ)
  diffAt-out = D.describes-out

  diffAt-in : fst (lookup k γ) ≡ fst (lookup i γ) ∖ fst (lookup j γ)
            → ⟨ γ ⊨ diffAt k i j ⟩
  diffAt-in = D.describes-in

unionAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
unionAt k i j =
  extAt k ((var zero ∈̇ var (suc i)) ∨̇ (var zero ∈̇ var (suc j)))

module _ {n : ℕ} (k i j : Fin n) (γ : S ^ n) where
  private
    Φ : Formula S (suc n)
    Φ = (var zero ∈̇ var (suc i)) ∨̇ (var zero ∈̇ var (suc j))

    A B : V ℓ
    A = fst (lookup i γ)
    B = fst (lookup j γ)

    module D = Describes k Φ γ (A ∪ B)
      (λ y y∈u → PT.rec (snd (isL y))
          (λ { (inl hA) → isL-trans {x = A} {y = y} hA (lookup i γ .snd)
             ; (inr hB) → isL-trans {x = B} {y = y} hB (lookup j γ .snd) })
          (∪-out {X = A} {Y = B} {x = y} y∈u))
      (λ z hz → PT.rec (snd (fst z ∈ A ∪ B))
          (λ { (inl hA) → ∪-left {X = A} {Y = B} {x = fst z} hA
             ; (inr hB) → ∪-right {X = A} {Y = B} {x = fst z} hB })
          hz)
      (λ z z∈u → ∪-out {X = A} {Y = B} {x = fst z} z∈u)

  unionAt-out : ⟨ γ ⊨ unionAt k i j ⟩
              → fst (lookup k γ) ≡ fst (lookup i γ) ∪ fst (lookup j γ)
  unionAt-out = D.describes-out

  unionAt-in : fst (lookup k γ) ≡ fst (lookup i γ) ∪ fst (lookup j γ)
             → ⟨ γ ⊨ unionAt k i j ⟩
  unionAt-in = D.describes-in
```

<!--en-->
## Product and the membership graph

The two relational bodies. Under the extension binder, two more binders pick
the components, each held to its argument slot by an atom, and the pair
formula pins the bound member as their Kuratowski pair; the membership graph
adds one atom between the components. The conversions unpack the two
existentials against the operation's fiber, and the constructibility of a
member is the constructibility of a pair of constructibles, which is the
sealed pair's own certificate carried across its projection equation.
<!--zh-->
## 积与隶属图

两个关系性的体。在外延束缚元之下，再有两个束缚元挑出分量，各由一条原子钉在自己的实参槽位上，而配对公式把被绑定的成员钉为它们的 Kuratowski 对；隶属图在两个分量之间多加一条原子。转换对着运算的纤维拆开两个存在量词，而成员的可构造性就是「可构造者之对」的可构造性，即封印配对自带的证书沿其投影等式搬过去。
<!--/-->

```agda
private
  shiftThree : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  shiftThree x = suc (suc (suc x))

  prIsL : (u v : V ℓ) → ⟨ isL u ⟩ → ⟨ isL v ⟩ → ⟨ isL (pr u v) ⟩
  prIsL u v hu hv =
    subst (λ w → ⟨ isL w ⟩) (prʟ-fst (u , hu) (v , hv))
      (prʟ (u , hu) (v , hv) .snd)

productAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
productAt k i j = extAt k (∃̇ (∃̇
  ( (var (suc zero) ∈̇ var (shiftThree i))
  ∧̇ ( (var zero ∈̇ var (shiftThree j))
    ∧̇ prAtL (suc (suc zero)) (suc zero) zero ) )))

module _ {n : ℕ} (k i j : Fin n) (γ : S ^ n) where
  private
    Body : Formula S (suc (suc (suc n)))
    Body = (var (suc zero) ∈̇ var (shiftThree i))
        ∧̇ ( (var zero ∈̇ var (shiftThree j))
          ∧̇ prAtL (suc (suc zero)) (suc zero) zero )

    A B : V ℓ
    A = fst (lookup i γ)
    B = fst (lookup j γ)

    module D = Describes k (∃̇ (∃̇ Body)) γ (product A B)
      (λ y y∈p → PT.rec (snd (isL y))
          (λ { (u , v , hu , hv , e) →
            subst (λ w → ⟨ isL w ⟩) (sym e)
              (prIsL u v
                (isL-trans {x = A} {y = u} hu (lookup i γ .snd))
                (isL-trans {x = B} {y = v} hv (lookup j γ .snd))) })
          (product-out {X = A} {Y = B} {w = y} y∈p))
      (λ z hz → PT.rec (snd (fst z ∈ product A B))
          (λ { (a , ha) → PT.rec (snd (fst z ∈ product A B))
            (λ { (b , (hA , (hB , hp))) →
              subst (λ w → ⟨ w ∈ product A B ⟩)
                (sym (subst ⟨_⟩
                  (prAtL-adequate (suc (suc zero)) (suc zero) zero
                    (b ∷ a ∷ z ∷ γ)) hp))
                (product-in {X = A} {Y = B} {u = fst a} {v = fst b} hA hB) })
            ha })
          hz)
      (λ z z∈p → PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ Body)))
          (λ { (u , v , hu , hv , e) →
            let a : S
                a = u , isL-trans {x = A} {y = u} hu (lookup i γ .snd)
                b : S
                b = v , isL-trans {x = B} {y = v} hv (lookup j γ .snd)
            in ∣ a , ∣ b , ( hu , ( hv
               , subst ⟨_⟩
                   (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                     (b ∷ a ∷ z ∷ γ))) e )) ∣₁ ∣₁ })
          (product-out {X = A} {Y = B} {w = fst z} z∈p))

  productAt-out : ⟨ γ ⊨ productAt k i j ⟩
                → fst (lookup k γ) ≡ product (fst (lookup i γ)) (fst (lookup j γ))
  productAt-out = D.describes-out

  productAt-in : fst (lookup k γ) ≡ product (fst (lookup i γ)) (fst (lookup j γ))
               → ⟨ γ ⊨ productAt k i j ⟩
  productAt-in = D.describes-in

memberGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
memberGraphAt k i j = extAt k (∃̇ (∃̇
  ( (var (suc zero) ∈̇ var (shiftThree i))
  ∧̇ ( (var zero ∈̇ var (shiftThree j))
    ∧̇ ( (var (suc zero) ∈̇ var zero)
      ∧̇ prAtL (suc (suc zero)) (suc zero) zero ) ) )))

module _ {n : ℕ} (k i j : Fin n) (γ : S ^ n) where
  private
    Body : Formula S (suc (suc (suc n)))
    Body = (var (suc zero) ∈̇ var (shiftThree i))
        ∧̇ ( (var zero ∈̇ var (shiftThree j))
          ∧̇ ( (var (suc zero) ∈̇ var zero)
            ∧̇ prAtL (suc (suc zero)) (suc zero) zero ) )

    A B : V ℓ
    A = fst (lookup i γ)
    B = fst (lookup j γ)

    module D = Describes k (∃̇ (∃̇ Body)) γ (memberGraph A B)
      (λ y y∈g → PT.rec (snd (isL y))
          (λ { (u , v , hu , hv , _ , e) →
            subst (λ w → ⟨ isL w ⟩) (sym e)
              (prIsL u v
                (isL-trans {x = A} {y = u} hu (lookup i γ .snd))
                (isL-trans {x = B} {y = v} hv (lookup j γ .snd))) })
          (memberGraph-out {X = A} {Y = B} {w = y} y∈g))
      (λ z hz → PT.rec (snd (fst z ∈ memberGraph A B))
          (λ { (a , ha) → PT.rec (snd (fst z ∈ memberGraph A B))
            (λ { (b , (hA , (hB , (hab , hp)))) →
              subst (λ w → ⟨ w ∈ memberGraph A B ⟩)
                (sym (subst ⟨_⟩
                  (prAtL-adequate (suc (suc zero)) (suc zero) zero
                    (b ∷ a ∷ z ∷ γ)) hp))
                (memberGraph-in {X = A} {Y = B} {u = fst a} {v = fst b}
                  hA hB hab) })
            ha })
          hz)
      (λ z z∈g → PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ Body)))
          (λ { (u , v , hu , hv , huv , e) →
            let a : S
                a = u , isL-trans {x = A} {y = u} hu (lookup i γ .snd)
                b : S
                b = v , isL-trans {x = B} {y = v} hv (lookup j γ .snd)
            in ∣ a , ∣ b , ( hu , ( hv , ( huv
               , subst ⟨_⟩
                   (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                     (b ∷ a ∷ z ∷ γ))) e ))) ∣₁ ∣₁ })
          (memberGraph-out {X = A} {Y = B} {w = fst z} z∈g))

  memberGraphAt-out : ⟨ γ ⊨ memberGraphAt k i j ⟩
                    → fst (lookup k γ)
                    ≡ memberGraph (fst (lookup i γ)) (fst (lookup j γ))
  memberGraphAt-out = D.describes-out

  memberGraphAt-in : fst (lookup k γ)
                   ≡ memberGraph (fst (lookup i γ)) (fst (lookup j γ))
                   → ⟨ γ ⊨ memberGraphAt k i j ⟩
  memberGraphAt-in = D.describes-in
```

<!--en-->
## Recap

One frame, `Describes`{.Agda}, turning a body and two semantic conversions
into an identity between a slot and an operation's value, and four
descriptions through it: `diffAt`{.Agda}, `unionAt`{.Agda}, `productAt`{.Agda}
and `memberGraphAt`{.Agda}, each read in both directions at variable slots and
a variable environment. The remaining operations of the stock, and the closure
step that disjoins all of them under one extension, take their descriptions
through the same frame in the chapter that binds them.
<!--zh-->
## 小结

一个框架 `Describes`{.Agda}，把一个体与两个语义转换变成「槽位与运算取值之间的等同」，以及经它而得的四条描述：`diffAt`{.Agda}、`unionAt`{.Agda}、`productAt`{.Agda} 与 `memberGraphAt`{.Agda}，每条都在变元槽位与变元环境处双向读出。存货中其余的运算，以及把它们全体析取在一个外延之下的闭包步，将在绑定它们的那一章经同一框架取得描述。
<!--/-->
