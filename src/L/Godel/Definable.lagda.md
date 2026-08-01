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
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; sucʟ; sucʟ-fst )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Coding.Base {ℓ} using ( ∈pair-introL; ∈pair-introR )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; extAt-in-both
        ; prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; sucAtL; sucAtL-adequate
        ; numL; envOverAt; svAt; domAt; valuesInAt; pairsInAt
        ; inDomAt; inDomAt-adequate; svAt-in; svAt-out; domAt-in
        ; valuesInAt-out; valuesInAt-in; pairsIn-in; pairsIn-out
        ; envOver-sv; envOver-dom; envOver-values; envOver-pairs )
open import L.Coding.InL {ℓ} using ( sglL )
open import L.Godel.Tuples {ℓ} using ( tuple; allTuples )
open import L.Godel.InL {ℓ} using ( allTuplesL; shiftDownL; extendFamilyL )
open import L.Godel.Operations {ℓ}
  using ( _∪_; ∪-left; ∪-right; ∪-out; _∖_; ∖-in; ∖-out
        ; _∩_; ∩-in; ∩-out
        ; product; product-in; product-out
        ; memberGraph; memberGraph-in; memberGraph-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; values; values-in; values-wit; singleton-self; singleton-out
        ; tailGraph; tailGraph-in; tailGraph-out
        ; shiftDown; shiftDown-in; shiftDown-out
        ; extendGraph; extendGraph-zero; extendGraph-suc; extendGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )

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
  shiftTwo : ∀ {n} → Fin n → Fin (suc (suc n))
  shiftTwo x = suc (suc x)

  shiftThree : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  shiftThree x = suc (suc (suc x))

  shiftFour : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  shiftFour x = suc (suc (suc (suc x)))

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
## Intersection, the selections, and the values

Four more descriptions for the denotation clauses to come. Intersection is
the cheapest body of all, two atoms under a conjunction. The two selections
are described at singleton keys, because that is how every denotation applies
them: the key slots hold the key values themselves, straight off a code's
payload, and the singleton wrapping stays on the meta side where its two
one-line laws discharge it. Their bodies bind the recorded values and speak
through the application reader, "this key records that value here". The
values operation pins its zero key by one object equality against the sealed
numeral. Constructibility of a member is transitivity walking the recorded
pair, exactly the walk the bridge chapter took at stages.
<!--zh-->
## 交、诸选择与取值集

为将来的指称子句再备四条描述。交是所有体中最便宜的，合取下两条原子。两个选择在单点键处描述，因为每个指称都这样应用它们：键槽位直接持有键的取值，恰是码的载荷所给，而单点集包装留在元层，由它的两条一行定律兑清。其体绑定被记录的取值，经应用读式说话，即「此键在此记录彼值」。取值集运算以一条对着封印数码的对象等式钉住零号键。成员的可构造性是传递性沿被记录的对行走，恰是桥梁章在阶段处走过的那趟。
<!--/-->

```agda
interAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
interAt k i j =
  extAt k ((var zero ∈̇ var (suc i)) ∧̇ (var zero ∈̇ var (suc j)))

module _ {n : ℕ} (k i j : Fin n) (γ : S ^ n) where
  private
    Φ : Formula S (suc n)
    Φ = (var zero ∈̇ var (suc i)) ∧̇ (var zero ∈̇ var (suc j))

    A B : V ℓ
    A = fst (lookup i γ)
    B = fst (lookup j γ)

    module D = Describes k Φ γ (A ∩ B)
      (λ y y∈c → isL-trans {x = A} {y = y}
          (∩-out {X = A} {Y = B} {x = y} y∈c .fst) (lookup i γ .snd))
      (λ z hz → ∩-in {X = A} {Y = B} {x = fst z} (hz .fst) (hz .snd))
      (λ z z∈c → ∩-out {X = A} {Y = B} {x = fst z} z∈c)

  interAt-out : ⟨ γ ⊨ interAt k i j ⟩
              → fst (lookup k γ) ≡ fst (lookup i γ) ∩ fst (lookup j γ)
  interAt-out = D.describes-out

  interAt-in : fst (lookup k γ) ≡ fst (lookup i γ) ∩ fst (lookup j γ)
             → ⟨ γ ⊨ interAt k i j ⟩
  interAt-in = D.describes-in

selectMemberAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
selectMemberAt k f a b = extAt k
  ( (var zero ∈̇ var (suc f))
  ∧̇ (∃̇ (∃̇ ( appAt (suc (suc zero)) (shiftThree a) (suc zero)
          ∧̇ ( appAt (suc (suc zero)) (shiftThree b) zero
            ∧̇ (var (suc zero) ∈̇ var zero) ) ))) )

module _ {n : ℕ} (k f a b : Fin n) (γ : S ^ n) where
  private
    Rest : Formula S (suc (suc (suc n)))
    Rest = appAt (suc (suc zero)) (shiftThree a) (suc zero)
        ∧̇ ( appAt (suc (suc zero)) (shiftThree b) zero
          ∧̇ (var (suc zero) ∈̇ var zero) )

    Φ : Formula S (suc n)
    Φ = (var zero ∈̇ var (suc f)) ∧̇ (∃̇ (∃̇ Rest))

    F Ka Kb : V ℓ
    F = fst (lookup f γ)
    Ka = fst (lookup a γ)
    Kb = fst (lookup b γ)

    Sel : V ℓ
    Sel = selectMember F ⁅ Ka ⁆s ⁅ Kb ⁆s

    readSel : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ Sel ⟩
    readSel z (hzf , big) = PT.rec (snd (fst z ∈ Sel))
      (λ { (u , hu) → PT.rec (snd (fst z ∈ Sel))
        (λ { (v , (h1 , (h2 , huv))) →
          selectMember-in {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z}
            {a = Ka} {b = Kb} {u = fst u} {v = fst v}
            hzf (singleton-self Ka) (singleton-self Kb)
            (subst ⟨_⟩ (appAt-adequate (suc (suc zero)) (shiftThree a)
              (suc zero) (v ∷ u ∷ z ∷ γ)) h1)
            (subst ⟨_⟩ (appAt-adequate (suc (suc zero)) (shiftThree b)
              zero (v ∷ u ∷ z ∷ γ)) h2)
            huv })
        hu })
      big

    fillSel : (z : S) → ⟨ fst z ∈ Sel ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    fillSel z z∈ =
      selectMember-sub {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z} z∈
      , PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ Rest))) build
          (selectMember-wit {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z} z∈)
      where
      build : Σ[ a' ∈ V ℓ ] Σ[ b' ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
              ( ⟨ a' ∈ ⁅ Ka ⁆s ⟩ × ⟨ b' ∈ ⁅ Kb ⁆s ⟩
              × ⟨ pr a' u ∈ fst z ⟩ × ⟨ pr b' v ∈ fst z ⟩ × ⟨ u ∈ v ⟩ )
            → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ Rest) ⟩
      build (a' , b' , u , v , ha' , hb' , hau , hbv , huv) =
        ∣ (u , uL) , ∣ (v , vL)
          , ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc zero)) (shiftThree a)
                (suc zero) ((v , vL) ∷ (u , uL) ∷ z ∷ γ))) hau'
            , ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc zero)) (shiftThree b)
                  zero ((v , vL) ∷ (u , uL) ∷ z ∷ γ))) hbv'
              , huv ) ) ∣₁ ∣₁
        where
        hau' : ⟨ pr Ka u ∈ fst z ⟩
        hau' = subst (λ w → ⟨ pr w u ∈ fst z ⟩) (singleton-out ha') hau
        hbv' : ⟨ pr Kb v ∈ fst z ⟩
        hbv' = subst (λ w → ⟨ pr w v ∈ fst z ⟩) (singleton-out hb') hbv
        uL : ⟨ isL u ⟩
        uL = isL-trans {x = ⁅ Ka , u ⁆} {y = u} (∈pair-introR refl)
          (isL-trans {x = pr Ka u} {y = ⁅ Ka , u ⁆} (∈pair-introR refl)
            (isL-trans {x = fst z} {y = pr Ka u} hau' (z .snd)))
        vL : ⟨ isL v ⟩
        vL = isL-trans {x = ⁅ Kb , v ⁆} {y = v} (∈pair-introR refl)
          (isL-trans {x = pr Kb v} {y = ⁅ Kb , v ⁆} (∈pair-introR refl)
            (isL-trans {x = fst z} {y = pr Kb v} hbv' (z .snd)))

    module D = Describes k Φ γ Sel
      (λ y y∈s → isL-trans {x = F} {y = y}
          (selectMember-sub {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = y} y∈s)
          (lookup f γ .snd))
      readSel fillSel

  selectMemberAt-out : ⟨ γ ⊨ selectMemberAt k f a b ⟩
    → fst (lookup k γ)
    ≡ selectMember (fst (lookup f γ)) ⁅ fst (lookup a γ) ⁆s ⁅ fst (lookup b γ) ⁆s
  selectMemberAt-out = D.describes-out

  selectMemberAt-in : fst (lookup k γ)
    ≡ selectMember (fst (lookup f γ)) ⁅ fst (lookup a γ) ⁆s ⁅ fst (lookup b γ) ⁆s
    → ⟨ γ ⊨ selectMemberAt k f a b ⟩
  selectMemberAt-in = D.describes-in

selectEqualAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
selectEqualAt k f a b = extAt k
  ( (var zero ∈̇ var (suc f))
  ∧̇ (∃̇ ( appAt (suc zero) (shiftTwo a) zero
        ∧̇ appAt (suc zero) (shiftTwo b) zero )) )

module _ {n : ℕ} (k f a b : Fin n) (γ : S ^ n) where
  private
    Rest : Formula S (suc (suc n))
    Rest = appAt (suc zero) (shiftTwo a) zero
        ∧̇ appAt (suc zero) (shiftTwo b) zero

    Φ : Formula S (suc n)
    Φ = (var zero ∈̇ var (suc f)) ∧̇ (∃̇ Rest)

    F Ka Kb : V ℓ
    F = fst (lookup f γ)
    Ka = fst (lookup a γ)
    Kb = fst (lookup b γ)

    Sel : V ℓ
    Sel = selectEqual F ⁅ Ka ⁆s ⁅ Kb ⁆s

    readSel : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ Sel ⟩
    readSel z (hzf , big) = PT.rec (snd (fst z ∈ Sel))
      (λ { (u , (h1 , h2)) →
        selectEqual-in {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z}
          {a = Ka} {b = Kb} {u = fst u}
          hzf (singleton-self Ka) (singleton-self Kb)
          (subst ⟨_⟩ (appAt-adequate (suc zero) (shiftTwo a)
            zero (u ∷ z ∷ γ)) h1)
          (subst ⟨_⟩ (appAt-adequate (suc zero) (shiftTwo b)
            zero (u ∷ z ∷ γ)) h2) })
      big

    fillSel : (z : S) → ⟨ fst z ∈ Sel ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    fillSel z z∈ =
      selectEqual-sub {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z} z∈
      , PT.rec (snd ((z ∷ γ) ⊨ ∃̇ Rest)) build
          (selectEqual-wit {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = fst z} z∈)
      where
      build : Σ[ a' ∈ V ℓ ] Σ[ b' ∈ V ℓ ] Σ[ u ∈ V ℓ ]
              ( ⟨ a' ∈ ⁅ Ka ⁆s ⟩ × ⟨ b' ∈ ⁅ Kb ⁆s ⟩
              × ⟨ pr a' u ∈ fst z ⟩ × ⟨ pr b' u ∈ fst z ⟩ )
            → ⟨ (z ∷ γ) ⊨ ∃̇ Rest ⟩
      build (a' , b' , u , ha' , hb' , hau , hbu) =
        ∣ (u , uL)
          , ( subst ⟨_⟩ (sym (appAt-adequate (suc zero) (shiftTwo a)
                zero ((u , uL) ∷ z ∷ γ))) hau'
            , subst ⟨_⟩ (sym (appAt-adequate (suc zero) (shiftTwo b)
                zero ((u , uL) ∷ z ∷ γ))) hbu' ) ∣₁
        where
        hau' : ⟨ pr Ka u ∈ fst z ⟩
        hau' = subst (λ w → ⟨ pr w u ∈ fst z ⟩) (singleton-out ha') hau
        hbu' : ⟨ pr Kb u ∈ fst z ⟩
        hbu' = subst (λ w → ⟨ pr w u ∈ fst z ⟩) (singleton-out hb') hbu
        uL : ⟨ isL u ⟩
        uL = isL-trans {x = ⁅ Ka , u ⁆} {y = u} (∈pair-introR refl)
          (isL-trans {x = pr Ka u} {y = ⁅ Ka , u ⁆} (∈pair-introR refl)
            (isL-trans {x = fst z} {y = pr Ka u} hau' (z .snd)))

    module D = Describes k Φ γ Sel
      (λ y y∈s → isL-trans {x = F} {y = y}
          (selectEqual-sub {X = F} {Ka = ⁅ Ka ⁆s} {Kb = ⁅ Kb ⁆s} {w = y} y∈s)
          (lookup f γ .snd))
      readSel fillSel

  selectEqualAt-out : ⟨ γ ⊨ selectEqualAt k f a b ⟩
    → fst (lookup k γ)
    ≡ selectEqual (fst (lookup f γ)) ⁅ fst (lookup a γ) ⁆s ⁅ fst (lookup b γ) ⁆s
  selectEqualAt-out = D.describes-out

  selectEqualAt-in : fst (lookup k γ)
    ≡ selectEqual (fst (lookup f γ)) ⁅ fst (lookup a γ) ⁆s ⁅ fst (lookup b γ) ⁆s
    → ⟨ γ ⊨ selectEqualAt k f a b ⟩
  selectEqualAt-in = D.describes-in

valuesAt : ∀ {n} → Fin n → Fin n → Formula S n
valuesAt k f = extAt k (∃̇ (∃̇
  ( (var (suc zero) ∈̇ var (shiftThree f))
  ∧̇ ( (var zero ≐ con (numeralL 0))
    ∧̇ appAt (suc zero) zero (suc (suc zero)) ) )))

module _ {n : ℕ} (k f : Fin n) (γ : S ^ n) where
  private
    Body : Formula S (suc (suc (suc n)))
    Body = (var (suc zero) ∈̇ var (shiftThree f))
        ∧̇ ( (var zero ≐ con (numeralL 0))
          ∧̇ appAt (suc zero) zero (suc (suc zero)) )

    F : V ℓ
    F = fst (lookup f γ)

    readVal : (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ Body) ⟩ → ⟨ fst z ∈ values F ⟩
    readVal z hz = PT.rec (snd (fst z ∈ values F))
      (λ { (g , hg) → PT.rec (snd (fst z ∈ values F))
        (λ { (k0 , (hgF , (ek , happ))) →
          values-in {X = F} {γ = fst g} {v = fst z} hgF
            (subst (λ w → ⟨ pr w (fst z) ∈ fst g ⟩)
              (ek ∙ numeralL-fst 0)
              (subst ⟨_⟩ (appAt-adequate (suc zero) zero
                (suc (suc zero)) (k0 ∷ g ∷ z ∷ γ)) happ)) })
        hg })
      hz

    fillVal : (z : S) → ⟨ fst z ∈ values F ⟩ → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ Body) ⟩
    fillVal z z∈ = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ Body))) build
      (values-wit {X = F} {v = fst z} z∈)
      where
      build : Σ[ g ∈ V ℓ ] (⟨ g ∈ F ⟩ × ⟨ pr (# 0) (fst z) ∈ g ⟩)
            → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ Body) ⟩
      build (g , hgF , hv) =
        ∣ (g , gL) , ∣ numeralL 0
          , ( hgF
            , ( refl
              , subst ⟨_⟩ (sym (appAt-adequate (suc zero) zero
                  (suc (suc zero)) (numeralL 0 ∷ (g , gL) ∷ z ∷ γ)))
                  (subst (λ w → ⟨ pr w (fst z) ∈ g ⟩)
                    (sym (numeralL-fst 0)) hv) ) ) ∣₁ ∣₁
        where
        gL : ⟨ isL g ⟩
        gL = isL-trans {x = F} {y = g} hgF (lookup f γ .snd)

    memVal : (y : V ℓ) → ⟨ y ∈ values F ⟩ → ⟨ isL y ⟩
    memVal y y∈ = PT.rec (snd (isL y))
      (λ { (g , hgF , hv) →
        isL-trans {x = ⁅ # 0 , y ⁆} {y = y} (∈pair-introR refl)
          (isL-trans {x = pr (# 0) y} {y = ⁅ # 0 , y ⁆} (∈pair-introR refl)
            (isL-trans {x = g} {y = pr (# 0) y} hv
              (isL-trans {x = F} {y = g} hgF (lookup f γ .snd)))) })
      (values-wit {X = F} {v = y} y∈)

    module D = Describes k (∃̇ (∃̇ Body)) γ (values F) memVal readVal fillVal

  valuesAt-out : ⟨ γ ⊨ valuesAt k f ⟩
               → fst (lookup k γ) ≡ values (fst (lookup f γ))
  valuesAt-out = D.describes-out

  valuesAt-in : fst (lookup k γ) ≡ values (fst (lookup f γ))
              → ⟨ γ ⊨ valuesAt k f ⟩
  valuesAt-in = D.describes-in
```

<!--en-->
## The tuple family, at an arity slot

The last leaf. A tuple is an environment graph, and the coding part already
owns the four-conjunct description of being one: single-valued, domain
pinned to a set, values bounded, and every member a recorded pair, each
conjunct with both readings. So the family of all tuples is described by one
extension whose body is that description with the domain slot holding the von
Neumann numeral of the arity, and what this section adds is only the two
conversions: recovering the assignment from the four conjuncts (the domain
gives an entry below every index, single-valuedness makes it a proposition,
so the truncation comes off), and filling the conjuncts back from a tuple's
own fibers. The arity enters as a meta number beside a slot equation, which
is how the denotation clauses will hand it over from a code's payload.
<!--zh-->
## 元数槽位处的元组族

最后一个叶。元组就是环境图，而编码部分已拥有「是一个环境图」的四合取描述：单值、定义域钉在某集合、取值有界、每个成员都是被记录的对，每条合取都带双向读式。于是全体元组之族由一个外延描述，其体正是那条描述、定义域槽位持有元数的冯·诺伊曼数码；本节新添的只有两个转换：从四条合取恢复赋值 (定义域给出每个序号以下的条目，单值性使它成为命题，截断便掉下来)，以及从元组自身的纤维把合取填回。元数以元层数字伴随一条槽位等式进场，指称子句将来正是这样从码的载荷把它递交过来。
<!--/-->

```agda
allTuplesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
allTuplesAt k x m = extAt k (envOverAt zero (suc m) (suc x))

module _ {n : ℕ} (k x m : Fin n) (γ : S ^ n) (arity : ℕ)
  (qm : fst (lookup m γ) ≡ # arity) where
  private
    A' : V ℓ
    A' = fst (lookup x γ)
    lA' : ⟨ isL A' ⟩
    lA' = lookup x γ .snd
    Tup : V ℓ
    Tup = allTuples A' arity

    nS : ℕ → S
    nS j = # j , numL j

    valA : (w : ⟪ A' ⟫) → ⟨ ⟪ A' ⟫↪ w ∈ A' ⟩
    valA w = ∈∈ₛ {a = ⟪ A' ⟫↪ w} {b = A'} .snd (∈ₛ⟪ A' ⟫↪ w)

    module Rec (z : S) (h : ⟨ (z ∷ γ) ⊨ envOverAt zero (suc m) (suc x) ⟩) where
      Entry : Fin arity → Type (ℓ-suc ℓ)
      Entry i = Σ[ y ∈ S ] ⟨ pr (# (toℕ i)) (fst y) ∈ fst z ⟩

      isPropEntry : (i : Fin arity) → isProp (Entry i)
      isPropEntry i (y , p) (y' , p') =
        Σ≡Prop (λ w → snd (pr (# (toℕ i)) (fst w) ∈ fst z))
          (Σ≡Prop (λ v → snd (isL v))
            (svAt-out zero (z ∷ γ)
              (envOver-sv zero (suc m) (suc x) (z ∷ γ) h)
              (nS (toℕ i)) y y' p p'))

      entry : (i : Fin arity) → Entry i
      entry i = PT.rec (isPropEntry i) (λ w → w)
        (domAt-in zero (suc m) (z ∷ γ)
          (envOver-dom zero (suc m) (suc x) (z ∷ γ) h)
          (nS (toℕ i))
          (subst (λ w → ⟨ # (toℕ i) ∈ w ⟩) (sym qm)
            (#mono (toℕ i) arity (toℕ<n i))))

      fib : (i : Fin arity) → Σ[ w ∈ ⟪ A' ⟫ ] (⟪ A' ⟫↪ w ≡ fst (entry i .fst))
      fib i = ∈-asFiber {a = fst (entry i .fst)} {b = A'}
        (valuesInAt-out zero (suc x) (z ∷ γ)
          (envOver-values zero (suc m) (suc x) (z ∷ γ) h)
          (nS (toℕ i)) (entry i .fst) (entry i .snd))

      g : Fin arity → ⟪ A' ⟫
      g i = fib i .fst

      recovers : fst z ≡ tuple A' g
      recovers = extensionalV λ w → ⇔toPath (bwd w) (fwd w)
        where
        fwd : (w : V ℓ) → ⟨ w ∈ tuple A' g ⟩ → ⟨ w ∈ fst z ⟩
        fwd w = PT.rec (snd (w ∈ fst z))
          λ { (li , q) → subst (λ u → ⟨ u ∈ fst z ⟩) q
                (subst (λ v → ⟨ pr (# (toℕ (lower li))) v ∈ fst z ⟩)
                  (sym (fib (lower li) .snd))
                  (entry (lower li) .snd)) }
        bwd : (w : V ℓ) → ⟨ w ∈ fst z ⟩ → ⟨ w ∈ tuple A' g ⟩
        bwd w hw = PT.rec PT.squash₁
          (λ { (u , v , u∈ , v∈ , eq) → PT.rec PT.squash₁
            (λ { (j , j<a , uj) → named u v eq j j<a uj })
            (∈#-elim arity (fst u)
              (subst (λ q' → ⟨ fst u ∈ q' ⟩) qm u∈)) })
          (pairsIn-out zero (suc m) (suc x) (z ∷ γ)
            (envOver-pairs zero (suc m) (suc x) (z ∷ γ) h)
            (w , isL-trans {x = fst z} {y = w} hw (z .snd)) hw)
          where
          named : (u v : S) → w ≡ pr (fst u) (fst v)
                → (j : ℕ) → j < arity → fst u ≡ # j
                → ⟨ w ∈ tuple A' g ⟩
          named u v eq j j<a uj =
            ∣ lift i , cong (pr (# (toℕ i))) (fib i .snd ∙ sym same)
                     ∙ cong (λ q' → pr q' (fst v)) iu ∙ sym eq ∣₁
            where
            i : Fin arity
            i = fromℕ' arity j j<a
            iu : # (toℕ i) ≡ fst u
            iu = cong #_ (toFromId' arity j j<a) ∙ sym uj
            hv : ⟨ pr (# (toℕ i)) (fst v) ∈ fst z ⟩
            hv = subst (λ q' → ⟨ q' ∈ fst z ⟩)
              (eq ∙ cong (λ q' → pr q' (fst v)) (sym iu)) hw
            same : fst v ≡ fst (entry i .fst)
            same = svAt-out zero (z ∷ γ)
              (envOver-sv zero (suc m) (suc x) (z ∷ γ) h)
              (nS (toℕ i)) v (entry i .fst) hv (entry i .snd)

    fill : (z : S) → ⟨ fst z ∈ Tup ⟩
         → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc m) (suc x) ⟩
    fill z z∈ = PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc m) (suc x)))
      (λ { (g , e) → build g e }) z∈
      where
      build : (g : Fin arity → ⟪ A' ⟫) → tuple A' g ≡ fst z
            → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc m) (suc x) ⟩
      build g e = sv , (dom , (vals , pairs))
        where
        out : (w : V ℓ) → ⟨ w ∈ fst z ⟩
            → ∥ Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin arity) ]
                (pr (# (toℕ (lower li))) (⟪ A' ⟫↪ (g (lower li))) ≡ w) ∥₁
        out w hw = subst (λ u → ⟨ w ∈ u ⟩) (sym e) hw

        into : (li : Lift {ℓ-zero} {ℓ} (Fin arity))
             → ⟨ pr (# (toℕ (lower li))) (⟪ A' ⟫↪ (g (lower li))) ∈ fst z ⟩
        into li = subst
          (λ u → ⟨ pr (# (toℕ (lower li))) (⟪ A' ⟫↪ (g (lower li))) ∈ u ⟩)
          e ∣ li , refl ∣₁

        sv : ⟨ (z ∷ γ) ⊨ svAt zero ⟩
        sv = svAt-in zero (z ∷ γ) λ x' y y' p q →
          PT.rec (setIsSet (fst y) (fst y'))
            (λ { (li , ei) → PT.rec (setIsSet (fst y) (fst y'))
              (λ { (lj , ej) → sym (pr-inj ei .snd)
                 ∙ cong (λ kk → ⟪ A' ⟫↪ (g kk))
                     (inj-toℕ (#-inj′ (pr-inj ei .fst ∙ sym (pr-inj ej .fst))))
                 ∙ pr-inj ej .snd })
              (out (pr (fst x') (fst y')) q) })
            (out (pr (fst x') (fst y)) p)

        dom : ⟨ (z ∷ γ) ⊨ domAt zero (suc m) ⟩
        dom x' = fwd' , bwd'
          where
          fwd' : ⟨ (x' ∷ z ∷ γ) ⊨ inDomAt (suc zero) zero ⟩
               → ⟨ fst x' ∈ fst (lookup m γ) ⟩
          fwd' hd = PT.rec (snd (fst x' ∈ fst (lookup m γ)))
            (λ { (y , p) → PT.rec (snd (fst x' ∈ fst (lookup m γ)))
              (λ { (li , ei) → subst (λ u → ⟨ u ∈ fst (lookup m γ) ⟩)
                     (pr-inj ei .fst)
                     (subst (λ u → ⟨ # (toℕ (lower li)) ∈ u ⟩) (sym qm)
                       (#mono (toℕ (lower li)) arity (toℕ<n (lower li)))) })
              (out (pr (fst x') (fst y)) p) })
            (subst ⟨_⟩ (inDomAt-adequate (suc zero) zero (x' ∷ z ∷ γ)) hd)

          bwd' : ⟨ fst x' ∈ fst (lookup m γ) ⟩
               → ⟨ (x' ∷ z ∷ γ) ⊨ inDomAt (suc zero) zero ⟩
          bwd' hx = subst ⟨_⟩
            (sym (inDomAt-adequate (suc zero) zero (x' ∷ z ∷ γ)))
            (PT.map
              (λ { (j , j<a , ex) →
                ( ⟪ A' ⟫↪ (g (fromℕ' arity j j<a))
                , isL-trans {x = A'} {y = ⟪ A' ⟫↪ (g (fromℕ' arity j j<a))}
                    (valA (g (fromℕ' arity j j<a))) lA' )
                , subst (λ u → ⟨ pr u (⟪ A' ⟫↪ (g (fromℕ' arity j j<a)))
                                  ∈ fst z ⟩)
                    (cong #_ (toFromId' arity j j<a) ∙ sym ex)
                    (into (lift (fromℕ' arity j j<a))) })
              (∈#-elim arity (fst x')
                (subst (λ u → ⟨ fst x' ∈ u ⟩) qm hx)))

        vals : ⟨ (z ∷ γ) ⊨ valuesInAt zero (suc x) ⟩
        vals = valuesInAt-in zero (suc x) (z ∷ γ) λ x' y hp →
          PT.rec (snd (fst y ∈ fst (lookup x γ)))
            (λ { (li , ei) → subst (λ u → ⟨ u ∈ fst (lookup x γ) ⟩)
                   (pr-inj ei .snd) (valA (g (lower li))) })
            (out (pr (fst x') (fst y)) hp)

        pairs : ⟨ (z ∷ γ) ⊨ pairsInAt zero (suc m) (suc x) ⟩
        pairs = pairsIn-in zero (suc m) (suc x) (z ∷ γ) λ s s∈ →
          PT.map
            (λ { (li , ei) →
                nS (toℕ (lower li))
              , ( ( ⟪ A' ⟫↪ (g (lower li))
                  , isL-trans {x = A'} {y = ⟪ A' ⟫↪ (g (lower li))}
                      (valA (g (lower li))) lA' )
                , ( subst (λ u → ⟨ # (toℕ (lower li)) ∈ u ⟩) (sym qm)
                      (#mono (toℕ (lower li)) arity (toℕ<n (lower li)))
                  , ( valA (g (lower li))
                    , sym ei ) ) ) })
            (out (fst s) s∈)

    module D = Describes k (envOverAt zero (suc m) (suc x)) γ Tup
      (λ y y∈t → isL-trans {x = Tup} {y = y} y∈t (allTuplesL A' lA' arity))
      (λ z hz → ∣ Rec.g z hz , sym (Rec.recovers z hz) ∣₁)
      fill

  allTuplesAt-out : ⟨ γ ⊨ allTuplesAt k x m ⟩
                  → fst (lookup k γ) ≡ allTuples (fst (lookup x γ)) arity
  allTuplesAt-out = D.describes-out

  allTuplesAt-in : fst (lookup k γ) ≡ allTuples (fst (lookup x γ)) arity
                 → ⟨ γ ⊨ allTuplesAt k x m ⟩
  allTuplesAt-in = D.describes-in
```

<!--en-->
## The shift

The first mover. A member of the shifted family is some family member's tail,
and the tail is pinned by the same two clauses the bridge chapter used at
stages, written here with unbounded binders because the class satisfaction
owes no bound: every member of the surveyed set is the shift of a recorded
successor pair, and every recorded successor pair reaches the surveyed set.
The successor witness travels through the coding part's successor reader, and
every existential witness is packaged by transitivity walking the pair, so
the conversions are the bridge chapter's readings with the formula plumbing
lighter by every waypoint.
<!--zh-->
## 移位

第一个移位运算。被移位族的成员是某个族成员的尾图，而尾图由桥梁章在阶段处用过的同样两条子句钉住，此处以无界束缚元写出，因为类满足不欠界：被检视集合的每个成员都是某个被记录后继对的移位，且每个被记录后继对都到达被检视集合。后继见证经编码部分的后继读式旅行，每个存在见证由传递性沿对行走打包，故转换就是桥梁章的读法，公式管线却每个中转站都轻掉。
<!--/-->

```agda
shiftDownAt : ∀ {n} → Fin n → Fin n → Formula S n
shiftDownAt k f = extAt k (∃̇
  ( (var zero ∈̇ var (shiftTwo f))
  ∧̇ ( (∀̇ ( (var zero ∈̇ var (suc (suc zero)))
         ⇒̇ (∃̇ (∃̇ (∃̇
              ( appAt (suc (suc (suc (suc zero)))) (suc zero) zero
              ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
                ∧̇ prAtL (suc (suc (suc zero))) (suc (suc zero)) zero )))))))
    ∧̇ (∀̇ (∀̇ (∀̇ ( ( appAt (suc (suc (suc zero))) (suc zero) zero
                  ∧̇ sucAtL (suc (suc zero)) (suc zero) )
                ⇒̇ appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero )))) ) ))

module _ {n : ℕ} (k f : Fin n) (γ : S ^ n) where
  private
    Seek : Formula S (suc (suc (suc n)))
    Seek = ∃̇ (∃̇ (∃̇
      ( appAt (suc (suc (suc (suc zero)))) (suc zero) zero
      ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
        ∧̇ prAtL (suc (suc (suc zero))) (suc (suc zero)) zero ))))

    Ψ : Formula S (suc (suc n))
    Ψ = (var zero ∈̇ var (shiftTwo f))
     ∧̇ ( (∀̇ ((var zero ∈̇ var (suc (suc zero))) ⇒̇ Seek))
       ∧̇ (∀̇ (∀̇ (∀̇ ( ( appAt (suc (suc (suc zero))) (suc zero) zero
                     ∧̇ sucAtL (suc (suc zero)) (suc zero) )
                   ⇒̇ appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero )))) )

    F' : V ℓ
    F' = fst (lookup f γ)
    lF' : ⟨ isL F' ⟩
    lF' = lookup f γ .snd

    T≡ : (z g : S)
       → ((w : S) → ⟨ fst w ∈ fst z ⟩ → ⟨ (w ∷ g ∷ z ∷ γ) ⊨ Seek ⟩)
       → ((a s v : S)
          → ⟨ (v ∷ s ∷ a ∷ g ∷ z ∷ γ)
                ⊨ ( appAt (suc (suc (suc zero))) (suc zero) zero
                  ∧̇ sucAtL (suc (suc zero)) (suc zero) ) ⟩
          → ⟨ (v ∷ s ∷ a ∷ g ∷ z ∷ γ)
                ⊨ appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero ⟩)
       → fst z ≡ tailGraph (fst g)
    T≡ z g membV imgV = extensionality (fst z) (tailGraph (fst g)) (t₁ , t₂)
      where
      t₁ : ⟨ fst z ⊆ tailGraph (fst g) ⟩
      t₁ w w∈ₛ = PT.rec (snd (w ∈ₛ tailGraph (fst g)))
        (λ { (a , ha) → PT.rec (snd (w ∈ₛ tailGraph (fst g)))
          (λ { (s , hs) → PT.rec (snd (w ∈ₛ tailGraph (fst g)))
            (λ { (v , (h1 , (h2 , h3))) → use a s v h1 h2 h3 })
            hs })
          ha })
        (membV wS w∈)
        where
        w∈ : ⟨ w ∈ fst z ⟩
        w∈ = ∈∈ₛ {a = w} {b = fst z} .snd w∈ₛ
        wS : S
        wS = w , isL-trans {x = fst z} {y = w} w∈ (z .snd)
        use : (a s v : S)
            → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                  ⊨ appAt (suc (suc (suc (suc zero)))) (suc zero) zero ⟩
            → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                  ⊨ sucAtL (suc (suc zero)) (suc zero) ⟩
            → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
            → ⟨ w ∈ₛ tailGraph (fst g) ⟩
        use a s v h1 h2 h3 = ∈∈ₛ {a = w} {b = tailGraph (fst g)} .fst
          (subst (λ u → ⟨ u ∈ tailGraph (fst g) ⟩) (sym e3)
            (tailGraph-in {w = fst g} {a = fst a} {v = fst v} h1'))
          where
          e2 : fst s ≡ sucV (fst a)
          e2 = subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc zero)
            (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h2
          e3 : w ≡ pr (fst a) (fst v)
          e3 = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
            (suc (suc zero)) zero (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h3
          h1' : ⟨ pr (sucV (fst a)) (fst v) ∈ fst g ⟩
          h1' = subst (λ u → ⟨ pr u (fst v) ∈ fst g ⟩) e2
            (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
              (suc zero) zero (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h1)
      t₂ : ⟨ tailGraph (fst g) ⊆ fst z ⟩
      t₂ w w∈ₛ = PT.rec (snd (w ∈ₛ fst z))
        (λ { (a , v , h , e) → named a v h e })
        (tailGraph-out {w = fst g} {z = w}
          (∈∈ₛ {a = w} {b = tailGraph (fst g)} .snd w∈ₛ))
        where
        named : (a v : V ℓ) → ⟨ pr (sucV a) v ∈ fst g ⟩ → w ≡ pr a v
              → ⟨ w ∈ₛ fst z ⟩
        named a v h e = ∈∈ₛ {a = w} {b = fst z} .fst
          (subst (λ u → ⟨ u ∈ fst z ⟩) (sym e)
            (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
              (suc (suc zero)) zero (vS ∷ sS ∷ aS ∷ g ∷ z ∷ γ))
              (imgV aS sS vS
                ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc zero)))
                    (suc zero) zero (vS ∷ sS ∷ aS ∷ g ∷ z ∷ γ))) h
                , subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) (suc zero)
                    (vS ∷ sS ∷ aS ∷ g ∷ z ∷ γ))) refl ))))
          where
          pL : ⟨ isL (pr (sucV a) v) ⟩
          pL = isL-trans {x = fst g} {y = pr (sucV a) v} h (g .snd)
          sL : ⟨ isL (sucV a) ⟩
          sL = isL-trans {x = ⁅ sucV a ⁆s} {y = sucV a} (singleton-self (sucV a))
            (isL-trans {x = pr (sucV a) v} {y = ⁅ sucV a ⁆s}
              (∈pair-introL refl) pL)
          aS sS vS : S
          aS = a , isL-trans {x = sucV a} {y = a} (self∈sucV a) sL
          sS = sucV a , sL
          vS = v , isL-trans {x = ⁅ sucV a , v ⁆} {y = v} (∈pair-introR refl)
            (isL-trans {x = pr (sucV a) v} {y = ⁅ sucV a , v ⁆}
              (∈pair-introR refl) pL)

    readSh : (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩ → ⟨ fst z ∈ shiftDown F' ⟩
    readSh z hz = PT.rec (snd (fst z ∈ shiftDown F'))
      (λ { (g , (hgF , (membV , imgV))) →
        subst (λ u → ⟨ u ∈ shiftDown F' ⟩) (sym (T≡ z g membV imgV))
          (shiftDown-in {X = F'} {z = fst g} hgF) })
      hz

    fillSh : (z : S) → ⟨ fst z ∈ shiftDown F' ⟩ → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩
    fillSh z z∈ = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ Ψ)) build
      (shiftDown-out {X = F'} {w = fst z} z∈)
      where
      build : Σ[ g' ∈ V ℓ ] (⟨ g' ∈ F' ⟩ × (tailGraph g' ≡ fst z))
            → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩
      build (g' , hg' , e) = ∣ gS , (hg' , (membV' , imgV')) ∣₁
        where
        gS : S
        gS = g' , isL-trans {x = F'} {y = g'} hg' lF'
        membV' : (w : S) → ⟨ fst w ∈ fst z ⟩ → ⟨ (w ∷ gS ∷ z ∷ γ) ⊨ Seek ⟩
        membV' w hw = PT.rec (snd ((w ∷ gS ∷ z ∷ γ) ⊨ Seek)) named
          (tailGraph-out {w = g'} {z = fst w}
            (subst (λ u → ⟨ fst w ∈ u ⟩) (sym e) hw))
          where
          named : Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                  (⟨ pr (sucV a) v ∈ g' ⟩ × (fst w ≡ pr a v))
                → ⟨ (w ∷ gS ∷ z ∷ γ) ⊨ Seek ⟩
          named (a , v , h , ew) =
            ∣ aS , ∣ sS , ∣ vS ,
              ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc zero))))
                  (suc zero) zero (vS ∷ sS ∷ aS ∷ w ∷ gS ∷ z ∷ γ))) h
              , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) (suc zero)
                    (vS ∷ sS ∷ aS ∷ w ∷ gS ∷ z ∷ γ))) refl
                , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) zero (vS ∷ sS ∷ aS ∷ w ∷ gS ∷ z ∷ γ))) ew ) )
            ∣₁ ∣₁ ∣₁
            where
            pL : ⟨ isL (pr (sucV a) v) ⟩
            pL = isL-trans {x = g'} {y = pr (sucV a) v} h (gS .snd)
            sL : ⟨ isL (sucV a) ⟩
            sL = isL-trans {x = ⁅ sucV a ⁆s} {y = sucV a}
              (singleton-self (sucV a))
              (isL-trans {x = pr (sucV a) v} {y = ⁅ sucV a ⁆s}
                (∈pair-introL refl) pL)
            aS sS vS : S
            aS = a , isL-trans {x = sucV a} {y = a} (self∈sucV a) sL
            sS = sucV a , sL
            vS = v , isL-trans {x = ⁅ sucV a , v ⁆} {y = v} (∈pair-introR refl)
              (isL-trans {x = pr (sucV a) v} {y = ⁅ sucV a , v ⁆}
                (∈pair-introR refl) pL)
        imgV' : (a s v : S)
              → ⟨ (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)
                    ⊨ ( appAt (suc (suc (suc zero))) (suc zero) zero
                      ∧̇ sucAtL (suc (suc zero)) (suc zero) ) ⟩
              → ⟨ (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)
                    ⊨ appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero ⟩
        imgV' a s v (h1 , h2) =
          subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc zero))))
            (suc (suc zero)) zero (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)))
            (subst (λ u → ⟨ pr (fst a) (fst v) ∈ u ⟩) e
              (tailGraph-in {w = g'} {a = fst a} {v = fst v}
                (subst (λ u → ⟨ pr u (fst v) ∈ g' ⟩)
                  (subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc zero)
                    (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)) h2)
                  (subst ⟨_⟩ (appAt-adequate (suc (suc (suc zero)))
                    (suc zero) zero (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)) h1))))

    module D = Describes k (∃̇ Ψ) γ (shiftDown F')
      (λ y y∈s → isL-trans {x = shiftDown F'} {y = y} y∈s (shiftDownL lF'))
      readSh fillSh

  shiftDownAt-out : ⟨ γ ⊨ shiftDownAt k f ⟩
                  → fst (lookup k γ) ≡ shiftDown (fst (lookup f γ))
  shiftDownAt-out = D.describes-out

  shiftDownAt-in : fst (lookup k γ) ≡ shiftDown (fst (lookup f γ))
                 → ⟨ γ ⊨ shiftDownAt k f ⟩
  shiftDownAt-in = D.describes-in
```


<!--en-->
## The extension
<!--zh-->
## 扩张
<!--/-->

<!--en-->
The second mover, at a singleton family like the selections, since that is how
every denotation applies it: the slot holds the new value itself. Three
clauses pin a member to the extension of a bound graph: every member is the
empty-key pair or the shift-up of a recorded pair, the empty-key pair is a
member, and every recorded pair's shift-up is a member. The empty key is one
object equality against the sealed zero numeral, and the successor witness on
the way in is packaged by the sealed successor, whose projection equation
makes its clause hold by `refl`{.Agda}.
<!--zh-->
第二个移位运算，与诸选择一样在单点族处描述，因为每个指称都这样应用它：槽位直接持有新取值。三条子句把成员钉在被绑图的扩张上：每个成员是空键对或某被记录对的上移、空键对是成员、每个被记录对的上移都是成员。空键是一条对着封印零数码的对象等式，而进入方向的后继见证由封印后继打包，其投影等式使那条子句由 `refl`{.Agda} 成立。
<!--/-->

```agda
extendFamilyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
extendFamilyAt k f y = extAt k (∃̇
  ( (var zero ∈̇ var (shiftTwo f))
  ∧̇ ( (∀̇ ( (var zero ∈̇ var (suc (suc zero)))
         ⇒̇ ( (∃̇ ( (var zero ≐ con (numeralL 0))
                ∧̇ prAtL (suc zero) zero (shiftFour y) ))
           ∨̇ (∃̇ (∃̇ (∃̇
                ( appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero
                ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
                  ∧̇ prAtL (suc (suc (suc zero))) (suc zero) zero ))))) )))
    ∧̇ ( (∃̇ ( (var zero ∈̇ var (suc (suc zero)))
           ∧̇ (∃̇ ( (var zero ≐ con (numeralL 0))
                ∧̇ prAtL (suc zero) zero (shiftFour y) ))))
      ∧̇ (∀̇ (∀̇ (∀̇ ( ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
                    ∧̇ sucAtL (suc (suc zero)) (suc zero) )
                  ⇒̇ appAt (suc (suc (suc (suc zero)))) (suc zero) zero )))) ) ) ))

module _ {n : ℕ} (k f y : Fin n) (γ : S ^ n) where
  private
    Z : Formula S (suc (suc (suc n)))
    Z = ∃̇ ( (var zero ≐ con (numeralL 0))
          ∧̇ prAtL (suc zero) zero (shiftFour y) )

    SE : Formula S (suc (suc (suc n)))
    SE = ∃̇ (∃̇ (∃̇
      ( appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero
      ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
        ∧̇ prAtL (suc (suc (suc zero))) (suc zero) zero ))))

    Ψ : Formula S (suc (suc n))
    Ψ = (var zero ∈̇ var (shiftTwo f))
     ∧̇ ( (∀̇ ((var zero ∈̇ var (suc (suc zero))) ⇒̇ (Z ∨̇ SE)))
       ∧̇ ( (∃̇ ((var zero ∈̇ var (suc (suc zero))) ∧̇ Z))
         ∧̇ (∀̇ (∀̇ (∀̇ ( ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
                       ∧̇ sucAtL (suc (suc zero)) (suc zero) )
                     ⇒̇ appAt (suc (suc (suc (suc zero)))) (suc zero) zero )))) ) )

    F' C : V ℓ
    F' = fst (lookup f γ)
    C = fst (lookup y γ)
    lF' : ⟨ isL F' ⟩
    lF' = lookup f γ .snd
    lC : ⟨ isL C ⟩
    lC = lookup y γ .snd

    e∅ : _≡_ {A = V ℓ} (# 0) ∅
    e∅ = refl

    zRead : (z g w : S) → ⟨ (w ∷ g ∷ z ∷ γ) ⊨ Z ⟩ → fst w ≡ pr ∅ C
    zRead z g w = PT.rec (setIsSet (fst w) (pr ∅ C))
      λ { (eS , (ek , hpr)) →
          subst ⟨_⟩ (prAtL-adequate (suc zero) zero (shiftFour y)
            (eS ∷ w ∷ g ∷ z ∷ γ)) hpr
        ∙ cong (λ u → pr u C) (ek ∙ numeralL-fst 0 ∙ e∅) }

    zBuild : (z g w : S) → fst w ≡ pr ∅ C → ⟨ (w ∷ g ∷ z ∷ γ) ⊨ Z ⟩
    zBuild z g w ew = ∣ (# 0 , numL 0)
      , ( sym (numeralL-fst 0)
        , subst ⟨_⟩ (sym (prAtL-adequate (suc zero) zero (shiftFour y)
            ((# 0 , numL 0) ∷ w ∷ g ∷ z ∷ γ)))
            (ew ∙ cong (λ u → pr u C) (sym e∅)) ) ∣₁

    module Pack (g : S) {a v : V ℓ} (h : ⟨ pr a v ∈ fst g ⟩) where
      pL : ⟨ isL (pr a v) ⟩
      pL = isL-trans {x = fst g} {y = pr a v} h (g .snd)
      aS vS sS : S
      aS = a , isL-trans {x = ⁅ a ⁆s} {y = a} (singleton-self a)
        (isL-trans {x = pr a v} {y = ⁅ a ⁆s} (∈pair-introL refl) pL)
      vS = v , isL-trans {x = ⁅ a , v ⁆} {y = v} (∈pair-introR refl)
        (isL-trans {x = pr a v} {y = ⁅ a , v ⁆} (∈pair-introR refl) pL)
      sS = sucV a , subst (λ u → ⟨ isL u ⟩) (sucʟ-fst aS) (sucʟ aS .snd)

    E≡ : (z g : S)
       → ((w : S) → ⟨ fst w ∈ fst z ⟩ → ⟨ (w ∷ g ∷ z ∷ γ) ⊨ (Z ∨̇ SE) ⟩)
       → ⟨ (g ∷ z ∷ γ) ⊨ ∃̇ ((var zero ∈̇ var (suc (suc zero))) ∧̇ Z) ⟩
       → ((a s v : S)
          → ⟨ (v ∷ s ∷ a ∷ g ∷ z ∷ γ)
                ⊨ ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
                  ∧̇ sucAtL (suc (suc zero)) (suc zero) ) ⟩
          → ⟨ (v ∷ s ∷ a ∷ g ∷ z ∷ γ)
                ⊨ appAt (suc (suc (suc (suc zero)))) (suc zero) zero ⟩)
       → fst z ≡ extendGraph C (fst g)
    E≡ z g membV imgZV imgSV =
      extensionality (fst z) (extendGraph C (fst g)) (e₁ , e₂)
      where
      e₁ : ⟨ fst z ⊆ extendGraph C (fst g) ⟩
      e₁ w w∈ₛ = PT.rec (snd (w ∈ₛ extendGraph C (fst g)))
        (λ { (inl zv) → zeroCase zv ; (inr sev) → sucCase sev })
        (membV wS w∈)
        where
        w∈ : ⟨ w ∈ fst z ⟩
        w∈ = ∈∈ₛ {a = w} {b = fst z} .snd w∈ₛ
        wS : S
        wS = w , isL-trans {x = fst z} {y = w} w∈ (z .snd)
        zeroCase : ⟨ (wS ∷ g ∷ z ∷ γ) ⊨ Z ⟩ → ⟨ w ∈ₛ extendGraph C (fst g) ⟩
        zeroCase zv = ∈∈ₛ {a = w} {b = extendGraph C (fst g)} .fst
          (subst (λ u → ⟨ u ∈ extendGraph C (fst g) ⟩)
            (sym (zRead z g wS zv))
            (extendGraph-zero {y = C} {γ = fst g}))
        sucCase : ⟨ (wS ∷ g ∷ z ∷ γ) ⊨ SE ⟩ → ⟨ w ∈ₛ extendGraph C (fst g) ⟩
        sucCase sev = PT.rec (snd (w ∈ₛ extendGraph C (fst g)))
          (λ { (a , ha) → PT.rec (snd (w ∈ₛ extendGraph C (fst g)))
            (λ { (s , hs) → PT.rec (snd (w ∈ₛ extendGraph C (fst g)))
              (λ { (v , (h1 , (h2 , h3))) → use a s v h1 h2 h3 })
              hs })
            ha })
          sev
          where
          use : (a s v : S)
              → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                    ⊨ appAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero ⟩
              → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                    ⊨ sucAtL (suc (suc zero)) (suc zero) ⟩
              → ⟨ (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)
                    ⊨ prAtL (suc (suc (suc zero))) (suc zero) zero ⟩
              → ⟨ w ∈ₛ extendGraph C (fst g) ⟩
          use a s v h1 h2 h3 = ∈∈ₛ {a = w} {b = extendGraph C (fst g)} .fst
            (subst (λ u → ⟨ u ∈ extendGraph C (fst g) ⟩)
              (sym ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                       (suc zero) zero (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h3
                   ∙ cong (λ u → pr u (fst v))
                       (subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc zero)
                         (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h2) ))
              (extendGraph-suc {y = C} {γ = fst g} {a = fst a} {v = fst v}
                (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
                  (suc (suc zero)) zero (v ∷ s ∷ a ∷ wS ∷ g ∷ z ∷ γ)) h1)))
      e₂ : ⟨ extendGraph C (fst g) ⊆ fst z ⟩
      e₂ w w∈ₛ = PT.rec (snd (w ∈ₛ fst z))
        (λ { (inl ez) → zeroCase ez
           ; (inr (a , v , h , ez)) → sucCase a v h ez })
        (extendGraph-out {y = C} {γ = fst g} {z = w}
          (∈∈ₛ {a = w} {b = extendGraph C (fst g)} .snd w∈ₛ))
        where
        zeroCase : w ≡ pr ∅ C → ⟨ w ∈ₛ fst z ⟩
        zeroCase ez = PT.rec (snd (w ∈ₛ fst z))
          (λ { (w₀ , (hw₀ , zv)) →
            ∈∈ₛ {a = w} {b = fst z} .fst
              (subst (λ u → ⟨ u ∈ fst z ⟩)
                (zRead z g w₀ zv ∙ sym ez) hw₀) })
          imgZV
        sucCase : (a v : V ℓ) → ⟨ pr a v ∈ fst g ⟩
                → w ≡ pr (sucV a) v → ⟨ w ∈ₛ fst z ⟩
        sucCase a v h ez = ∈∈ₛ {a = w} {b = fst z} .fst
          (subst (λ u → ⟨ u ∈ fst z ⟩) (sym ez)
            (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc zero))))
              (suc zero) zero (P.vS ∷ P.sS ∷ P.aS ∷ g ∷ z ∷ γ))
              (imgSV P.aS P.sS P.vS
                ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) zero (P.vS ∷ P.sS ∷ P.aS ∷ g ∷ z ∷ γ))) h
                , subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) (suc zero)
                    (P.vS ∷ P.sS ∷ P.aS ∷ g ∷ z ∷ γ))) refl ))))
          where
          module P = Pack g {a} {v} h

    readEx : (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩
           → ⟨ fst z ∈ extendFamily F' ⁅ C ⁆s ⟩
    readEx z hz = PT.rec (snd (fst z ∈ extendFamily F' ⁅ C ⁆s))
      (λ { (g , (hgF , (membV , (imgZV , imgSV)))) →
        subst (λ u → ⟨ u ∈ extendFamily F' ⁅ C ⁆s ⟩)
          (sym (E≡ z g membV imgZV imgSV))
          (extendFamily-in {X = F'} {Y = ⁅ C ⁆s} hgF (singleton-self C)) })
      hz

    fillEx : (z : S) → ⟨ fst z ∈ extendFamily F' ⁅ C ⁆s ⟩
           → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩
    fillEx z z∈ = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ Ψ)) build
      (extendFamily-out {X = F'} {Y = ⁅ C ⁆s} {w = fst z} z∈)
      where
      build : Σ[ g' ∈ V ℓ ] Σ[ y' ∈ V ℓ ]
              (⟨ g' ∈ F' ⟩ × ⟨ y' ∈ ⁅ C ⁆s ⟩ × (fst z ≡ extendGraph y' g'))
            → ⟨ (z ∷ γ) ⊨ ∃̇ Ψ ⟩
      build (g' , y' , hg' , hy' , e0) =
        ∣ gS , (hg' , (membV' , (imgZV' , imgSV'))) ∣₁
        where
        gS : S
        gS = g' , isL-trans {x = F'} {y = g'} hg' lF'
        e : fst z ≡ extendGraph C g'
        e = e0 ∙ cong (λ u → extendGraph u g') (singleton-out hy')
        membV' : (w : S) → ⟨ fst w ∈ fst z ⟩
               → ⟨ (w ∷ gS ∷ z ∷ γ) ⊨ (Z ∨̇ SE) ⟩
        membV' w hw = PT.rec (snd ((w ∷ gS ∷ z ∷ γ) ⊨ (Z ∨̇ SE)))
          (λ { (inl ez) → ∣ inl (zBuild z gS w ez) ∣₁
             ; (inr (a , v , h , ez)) → ∣ inr (seBuild a v h ez) ∣₁ })
          (extendGraph-out {y = C} {γ = g'} {z = fst w}
            (subst (λ u → ⟨ fst w ∈ u ⟩) e hw))
          where
          seBuild : (a v : V ℓ) → ⟨ pr a v ∈ g' ⟩ → fst w ≡ pr (sucV a) v
                  → ⟨ (w ∷ gS ∷ z ∷ γ) ⊨ SE ⟩
          seBuild a v h ez =
            ∣ P.aS , ∣ P.sS , ∣ P.vS ,
              ( subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc zero))))
                  (suc (suc zero)) zero
                  (P.vS ∷ P.sS ∷ P.aS ∷ w ∷ gS ∷ z ∷ γ))) h
              , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) (suc zero)
                    (P.vS ∷ P.sS ∷ P.aS ∷ w ∷ gS ∷ z ∷ γ))) refl
                , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
                    (suc zero) zero
                    (P.vS ∷ P.sS ∷ P.aS ∷ w ∷ gS ∷ z ∷ γ))) ez ) )
            ∣₁ ∣₁ ∣₁
            where
            module P = Pack gS {a} {v} h
        imgZV' : ⟨ (gS ∷ z ∷ γ) ⊨ ∃̇ ((var zero ∈̇ var (suc (suc zero))) ∧̇ Z) ⟩
        imgZV' = ∣ w₀S , (hw₀ , zBuild z gS w₀S refl) ∣₁
          where
          hw₀' : ⟨ pr ∅ C ∈ fst z ⟩
          hw₀' = subst (λ u → ⟨ pr ∅ C ∈ u ⟩) (sym e)
            (extendGraph-zero {y = C} {γ = g'})
          w₀S : S
          w₀S = pr ∅ C , isL-trans {x = fst z} {y = pr ∅ C} hw₀' (z .snd)
          hw₀ : ⟨ fst w₀S ∈ fst z ⟩
          hw₀ = hw₀'
        imgSV' : (a s v : S)
               → ⟨ (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)
                     ⊨ ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
                       ∧̇ sucAtL (suc (suc zero)) (suc zero) ) ⟩
               → ⟨ (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)
                     ⊨ appAt (suc (suc (suc (suc zero)))) (suc zero) zero ⟩
        imgSV' a s v (h1 , h2) =
          subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc zero))))
            (suc zero) zero (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)))
            (subst (λ u → ⟨ pr u (fst v) ∈ fst z ⟩)
              (sym (subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc zero)
                (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)) h2))
              (subst (λ u → ⟨ pr (sucV (fst a)) (fst v) ∈ u ⟩) (sym e)
                (extendGraph-suc {y = C} {γ = g'} {a = fst a} {v = fst v}
                  (subst ⟨_⟩ (appAt-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) zero (v ∷ s ∷ a ∷ gS ∷ z ∷ γ)) h1))))

    module D = Describes k (∃̇ Ψ) γ (extendFamily F' ⁅ C ⁆s)
      (λ y' y'∈ → isL-trans {x = extendFamily F' ⁅ C ⁆s} {y = y'} y'∈
        (extendFamilyL lF' (sglL lC)))
      readEx fillEx

  extendFamilyAt-out : ⟨ γ ⊨ extendFamilyAt k f y ⟩
    → fst (lookup k γ) ≡ extendFamily (fst (lookup f γ)) ⁅ fst (lookup y γ) ⁆s
  extendFamilyAt-out = D.describes-out

  extendFamilyAt-in : fst (lookup k γ)
    ≡ extendFamily (fst (lookup f γ)) ⁅ fst (lookup y γ) ⁆s
    → ⟨ γ ⊨ extendFamilyAt k f y ⟩
  extendFamilyAt-in = D.describes-in
```

<!--en-->
## Recap

One frame, `Describes`{.Agda}, turning a body and two semantic conversions
into an identity between a slot and an operation's value, and eleven
descriptions through it: `diffAt`{.Agda}, `unionAt`{.Agda}, `productAt`{.Agda}
and `memberGraphAt`{.Agda}, then `interAt`{.Agda}, the two selections at
singleton keys, `valuesAt`{.Agda}, the tuple family at an arity slot, and the
two graph movers, each read in both directions at variable slots and a
variable environment. Every operation a denotation clause will mention now
carries its description, and the clauses themselves are the next chapter's
business.
<!--zh-->
## 小结

一个框架 `Describes`{.Agda}，把一个体与两个语义转换变成「槽位与运算取值之间的等同」，以及经它而得的十一条描述：`diffAt`{.Agda}、`unionAt`{.Agda}、`productAt`{.Agda} 与 `memberGraphAt`{.Agda}，继而 `interAt`{.Agda}、单点键处的两个选择、`valuesAt`{.Agda}、元数槽位处的元组族，与两个图移位运算，每条都在变元槽位与变元环境处双向读出。指称子句将要提到的每个运算如今都带上了自己的描述，而子句本身是下一章的事。
<!--/-->
