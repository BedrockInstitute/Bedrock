# Descending into a code

<!--en-->
A recursion on codes has to get from a code to its parts, and membership will
not take it there. Kuratowski's pair puts a part four membership steps below the
tagged code that holds it, and the sets in between are not codes, so an
induction on membership cannot carry a hypothesis about codes across them.

Rank can. It increases strictly along membership, so four steps compose into one
by transitivity of ordinals, and the recursion then runs on the rank rather than
on the code. This chapter is those four steps, once for each side of a pair.

The chapter is small and it is the whole reason the seal on `rank`{.Agda} exists:
a goal mentioning the rank of a pair inside a pair inside a pair took 163 seconds
before that seal and 1.4 after.
<!--zh-->
一场跑在码上的递归必须从一条码走到它的诸部件，而成员关系送不了它到那里。Kuratowski 的对把一个部件放在「持有它的那条带标签的码」之下**四个**成员步之处，而中间那些集合不是码，故一场跑在成员关系上的归纳无法把「关于码的假设」搬过它们。

秩可以。秩沿成员关系严格增长，故四步经序数的传递性合成为一步，而递归随后跑在**秩**上、不跑在码上。本章就是那四步，对偶的每一侧各一次。

本章很小，而它正是 `rank`{.Agda} 那道封印存在的全部理由：一个提到「对里的对里的对」之秩的目标，封印之前 163 秒，之后 1.4 秒。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Descent {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-ord )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The steps
<!--zh-->
## 诸步
<!--/-->

<!--en-->
Membership in a singleton and in an unordered pair, stated as the introductions
the chain below wants, and the chain itself at four variable sets. Stating it at
variables and applying it once is what keeps a proof from unfolding four nested
pairs at each of three transitivity steps.
<!--zh-->
属于单点集与属于无序对，按下面那条链所要的引入形式陈述；再加上那条链本身，在四个变元集合上。陈述在变元上、再施用一次，正是使证明不必在三次传递性的每一次处都展开四层嵌套对的那件事。
<!--/-->

```agda
self∈singl : (a : S) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
self∈singl a = SetPackage.classification (SingletonPackage a) a .snd refl

pair∈ : (u v w : S) → (w ≡ u) ⊎ (w ≡ v) → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
pair∈ u v w h = ∈∈ₛ {a = w} {b = ⁅ u , v ⁆} .snd (pairing-ax u v w .snd ∣ h ∣₁)

trans≺ : (x y z : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank y ∈ˢ rank z ⟩ → ⟨ rank x ∈ˢ rank z ⟩
trans≺ x y z x∈y ry∈rz = rank-ord z .fst (rank-mono x y x∈y) ry∈rz

chain4 : (x y z w v : S) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ z ⟩ → ⟨ z ∈ˢ w ⟩ → ⟨ w ∈ˢ v ⟩
       → ⟨ rank x ∈ˢ rank v ⟩
chain4 x y z w v x∈y y∈z z∈w w∈v =
  trans≺ x y v x∈y (trans≺ y z v y∈z (trans≺ z w v z∈w (rank-mono w v w∈v)))
```

<!--en-->
## Into a tagged payload
<!--zh-->
## 进入带标签的载荷
<!--/-->

<!--en-->
A tagged code is a pair whose second component is the payload, and a payload is
either a code or a pair of them. So there are three descents to name: into a
payload, and into each side of a payload that is a pair. The tag itself is never
descended into, which is why it appears as an arbitrary set rather than as a
numeral.
<!--zh-->
一条带标签的码是一个对，其第二分量即载荷；而载荷要么是一条码、要么是两条码构成的对。故要点名的下降有三条：进入载荷，以及进入「载荷是对」时的两侧。标签本身从不被下降进去，这也是它以任意集合、而非以数码的形式出现的原因。
<!--/-->

```agda
payload≺ : (c z : S) → ⟨ rank z ∈ˢ rank (pr c z) ⟩
payload≺ c z = trans≺ z ⁅ c , z ⁆ (pr c z)
  (pair∈ c z z (inr refl))
  (rank-mono ⁅ c , z ⁆ (pr c z) (pair∈ ⁅ c ⁆s ⁅ c , z ⁆ ⁅ c , z ⁆ (inr refl)))

leftPart : (c a b : S) → ⟨ rank a ∈ˢ rank (pr c (pr a b)) ⟩
leftPart c a b = chain4 a ⁅ a ⁆s (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
  (∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd (self∈singl a))
  (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s (inl refl))
  (pair∈ c (pr a b) (pr a b) (inr refl))
  (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ (inr refl))

rightPart : (c a b : S) → ⟨ rank b ∈ˢ rank (pr c (pr a b)) ⟩
rightPart c a b = chain4 b ⁅ a , b ⁆ (pr a b) ⁅ c , pr a b ⁆ (pr c (pr a b))
  (pair∈ a b b (inr refl))
  (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl))
  (pair∈ c (pr a b) (pr a b) (inr refl))
  (pair∈ ⁅ c ⁆s ⁅ c , pr a b ⁆ ⁅ c , pr a b ⁆ (inr refl))
```
