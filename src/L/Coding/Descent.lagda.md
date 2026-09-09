<!--en-->
# Rank descent through coded pairs

Later well-founded recursions must move from a code to its immediate components. This chapter proves that each component of an ordered pair, and especially the payload of a tagged code, has strictly smaller rank than the whole code.
<!--zh-->
# 沿编码对作秩下降

后续良基递归需要从编码走向其直接部件。本章证明有序对的每个部件，特别是带标签编码的载荷，其秩都严格小于整个编码的秩。
<!--ja-->
# 符号化された対に沿う階数降下

後の整礎再帰では、コードからその直下の成分へ移る必要がある。本章では順序対の各成分、とくにタグ付きコードのペイロードが、コード全体より真に小さい階数をもつことを示す。
<!--/-->

<!--en-->
A recursion on codes has to get from a code to its parts, and membership will
not take it there. Kuratowski's pair puts a part four membership steps below the
tagged code that holds it, and the sets in between are not codes, so an
induction on membership cannot carry a hypothesis about codes across them.

Rank can. It increases strictly along membership, so four steps compose into one
by transitivity of ordinals, and the recursion then runs on the rank rather than
on the code. This chapter composes the same two-step descent for each side of a pair.

The chapter is small and it is the whole reason the seal on `rank`{.Agda} exists:
a goal mentioning the rank of a pair inside a pair inside a pair took 163 seconds
before that seal and 1.4 after.
<!--zh-->
一场跑在码上的递归必须从一条码走到它的诸部件，而成员关系送不了它到那里。Kuratowski 的对把一个部件放在「持有它的那条带标签的码」之下**四个**成员步之处，而中间那些集合不是码，故一场跑在成员关系上的归纳无法把「关于码的假设」搬过它们。

秩可以。秩沿成员关系严格增长，故四步经序数的传递性合成为一步，而递归随后跑在**秩**上、不跑在码上。本章为对偶的每一侧合成同一条两步下降。

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
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The steps
<!--zh-->
## 诸步
<!--ja-->
## 階数を下げる基本段階
<!--/-->

<!--en-->
Membership in an unordered pair selects one of its two components. Combining that fact with rank monotonicity turns membership of a component into a strict decrease of ranks.
<!--zh-->
无序对中的隶属关系会选出两个部件之一。把这一事实与秩的单调性结合，即可把部件隶属化为严格的秩下降。
<!--ja-->
非順序対への所属から二つの成分の一方が選ばれる。この事実と階数の単調性を組み合わせると、成分への所属を階数の真の減少へ変えられる。
<!--/-->

<!--en-->
Membership in an unordered pair supplies either component. The rank step
composes this membership with a rank inequality at variable sets, keeping the
nested pair expressions out of the transitivity proof.
<!--zh-->
无序对的隶属关系给出任一分量。秩的步骤在变元集合上把这条隶属关系与秩不等式合成，使嵌套对表达式不必进入传递性证明。
<!--/-->

```agda
pair∈ : (u v w : S) → (w ≡ u) ⊎ (w ≡ v) → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
pair∈ u v w h = ∈∈ₛ {a = w} {b = ⁅ u , v ⁆} .snd (pairing-ax u v w .snd ∣ h ∣₁)

trans≺ : (x y z : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank y ∈ˢ rank z ⟩ → ⟨ rank x ∈ˢ rank z ⟩
trans≺ x y z x∈y ry∈rz = rank-ord z .fst (rank-mono x y x∈y) ry∈rz

```

<!--en-->
## Into a tagged payload
<!--zh-->
## 进入带标签的载荷
<!--ja-->
## タグ付きコードのペイロードへ降りる
<!--/-->

<!--en-->
A tagged payload is nested inside two ordered pairs. Applying the component decrease at each layer proves separate descent lemmas for the left part, right part, and payload.
<!--zh-->
带标签的载荷嵌套在两层有序对内。逐层应用部件下降，即得左部件、右部件与载荷各自的下降引理。
<!--ja-->
タグ付きペイロードは二重の順序対の内側にある。各層で成分の降下を適用すると、左成分、右成分、ペイロードそれぞれの降下補題が得られる。
<!--/-->

<!--en-->
A tagged code is a pair whose second component is the payload, and a payload is
either a code or a pair of them. So there are three descents to name: into a
payload, and into each side of a payload that is a pair. The tag itself is never
descended into, which is why it appears as an arbitrary set rather than as a
numeral. Both components pass through the unordered pair in a Kuratowski
pair, so one two-step lemma handles either side. Applying it twice gives the
four-step descents into a paired payload.
<!--zh-->
一条带标签的码是一个对，其第二分量即载荷；而载荷要么是一条码，要么是两条码构成的对。故要点名的下降有三条：进入载荷，以及进入「载荷是对」时的两侧。标签本身从不被下降进去，这也是它以任意集合而非以数码的形式出现的原因。两个分量都经由 Kuratowski 对中的无序对，故一条两步引理处理任一侧。施用两次，便得到进入成对载荷的四步下降。
<!--/-->

```agda
pair-component≺ : (a b x : S) → (x ≡ a) ⊎ (x ≡ b) → ⟨ rank x ∈ˢ rank (pr a b) ⟩
pair-component≺ a b x h = trans≺ x ⁅ a , b ⁆ (pr a b) (pair∈ a b x h)
  (rank-mono ⁅ a , b ⁆ (pr a b) (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl)))

payload≺ : (c z : S) → ⟨ rank z ∈ˢ rank (pr c z) ⟩
payload≺ c z = pair-component≺ c z z (inr refl)

leftPart : (c a b : S) → ⟨ rank a ∈ˢ rank (pr c (pr a b)) ⟩
leftPart c a b = rank-ord (pr c (pr a b)) .fst
  (pair-component≺ a b a (inl refl)) (payload≺ c (pr a b))

rightPart : (c a b : S) → ⟨ rank b ∈ˢ rank (pr c (pr a b)) ⟩
rightPart c a b = rank-ord (pr c (pr a b)) .fst (payload≺ a b) (payload≺ c (pr a b))
```
