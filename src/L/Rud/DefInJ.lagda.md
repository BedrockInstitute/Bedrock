# The Def successor at a rud level

<!--en-->
The bridge's successor step is one ω-block up, and this chapter's share of
that step is two facts about a single Def stage. The first is the successor
collapse: a stage at a successor index is the definable power of the stage
below it, on the nose. The equation is what turns the successor statement
into a statement about a single set.

The second fact is the containment half at a limit: a limit rud level that
holds a constructible stage holds every definable subset of it, one formula
at a time, by the satisfaction engine read at that carrier. What is gone is
the old same-index discharge. The statement that one Def stage up stays a
member of the same limit level is false, recorded as such in the bridge
(Devlin VI.2.4), and the corrected successor statement lands one ω-block up
instead; nothing here reintroduces the false per-level identification.
<!--zh-->
桥的后继步整体向上一个 ω 块，而本章对那一步的分内之事，是关于单个 Def
阶段的两条事实。第一条是后继坍缩：后继索引处的阶段，恰是其下阶段的可定义幂。这条等式正是把后继陈述转成关于单个集合的陈述之物。

第二条事实是极限处的包含那一半：持有某可构造阶段的极限初步函数层，经满足集引擎在该载体处读出，一次一条公式地持有它的每个可定义子集。旧的同索引兑付已经不在。上升一个 Def 阶段仍为同一极限层的成员，这条陈述是假的，已在桥中如实记下 (Devlin VI.2.4)，而修正后的后继陈述改落在高出一个 ω 块之处；本章不重新引入那条假的逐层认同。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.DefInJ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using
  ( Lset; Lset-in; Lset-out; Lset-layer; layer-trans
  ; 𝒟ₒ; 𝒟ₒ-inv; Lset⊆𝒟ₒ )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-trans; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The successor collapse
<!--zh-->
## 后继坍缩
<!--/-->

<!--en-->
The stage at a successor index is the definable power of the stage below it,
on the nose. Going up is the tower's own introduction at the index's largest
member; coming down splits a member of the successor into a strictly smaller
index or the index itself, and the strictly smaller case is absorbed because
a stage is one of its own definable subsets.
<!--zh-->
后继索引处的阶段，恰是其下阶段的可定义幂。上行是塔在该索引最大成员处自带的引入；下行把后继的一个成员分成严格更小的索引或索引自身，而严格更小的情形被吸收，因为阶段是自己的可定义子集之一。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

Lsuc≡Def : (ζ : S) → Lset (sucV ζ) ≡ 𝒟ₒ (Lset ζ)
Lsuc≡Def ζ = ext-⊆ sub sup
  where
  sub : (x : S) → ⟨ x ∈ˢ Lset (sucV ζ) ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩
  sub x h = PT.rec (snd (x ∈ˢ 𝒟ₒ (Lset ζ))) go (Lset-out (sucV ζ) x h)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ sucV ζ ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩
    go (δ , δ∈ , hx) = ∈sucV-elim {A = ζ} {x = δ}
      (snd (x ∈ˢ 𝒟ₒ (Lset ζ))) δ∈
      (λ δ∈ζ → Lset⊆𝒟ₒ ζ x (Lset-in ζ δ x δ∈ζ hx))
      (λ δ≡ζ → subst (λ w → ⟨ x ∈ˢ 𝒟ₒ (Lset w) ⟩) δ≡ζ hx)
  sup : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
  sup x h = Lset-in (sucV ζ) ζ x (self∈sucV ζ) h
```

<!--en-->
## Definable subsets at a limit level
<!--zh-->
## 极限层处的可定义子集
<!--/-->

<!--en-->
The satisfaction engine is abstract in its carrier, so it applies to a
constructible stage held by a rud level just as well as to any other set:
every definable subset of the stage is a member of the limit level above the
one holding it. This is the containment half of the re-typed successor
story, delivered only where a limit level is available, and it survives as
the kept rud-into-`L` half's asset rather than as an obligation of the
reshaped induction.
<!--zh-->
满足集引擎对其载体是抽象的，故它施于初步函数层所持有的可构造阶段，与施于任何别的集合一样合用：该阶段的每个可定义子集，都是持有它的那一层之上那个极限层的成员。这是重述后的后继故事中已交付的包含那一半，只在有极限层可用之处交付，它作为被保留的初步函数进 `L` 那一半的资产而存续，而非重塑后归纳的义务。
<!--/-->

```agda
defs-in-limit : (ζ μ : S) → (limμ : ⟨ isLimit μ ⟩) → ⟨ Lset ζ ∈ˢ Sset μ ⟩
              → (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ y ∈ˢ Sset μ ⟩
defs-in-limit ζ μ limμ L∈ y y∈𝒟 =
  PT.rec (snd (y ∈ˢ Sset μ)) go (𝒟ₒ-inv (Lset ζ) y y∈𝒟)
  where
  Ltr : (u v : S) → ⟨ u ∈ˢ v ⟩ → ⟨ v ∈ˢ Lset ζ ⟩ → ⟨ u ∈ˢ Lset ζ ⟩
  Ltr u v u∈v v∈L = layer-trans (Lset-layer ζ) {x = v} {y = u} u∈v v∈L
  Jtr : (u v : S) → ⟨ v ∈ˢ Sset μ ⟩ → ⟨ u ∈ˢ v ⟩ → ⟨ u ∈ˢ Sset μ ⟩
  Jtr u v v∈J u∈v = Sset-trans μ {x = v} {y = u} u∈v v∈J
  module Sζ = Sat (Lset ζ) Ltr (λ z → ⟨ z ∈ˢ Sset μ ⟩) Jtr
                  (Jset-rud μ limμ) L∈
  go : Σ[ φ ∈ Formula ⟪ Lset ζ ⟫ 1 ] (DefOf.defSet (Lset ζ) φ ≡ y)
     → ⟨ y ∈ˢ Sset μ ⟩
  go (φ , eq) = subst (λ w → ⟨ w ∈ˢ Sset μ ⟩) eq (Sζ.defSet-InJ φ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter's two surviving facts are the successor collapse (`Lsuc≡Def`{.Agda}),
which turns the successor statement into a statement about the definable
power, and the containment half at a limit (`defs-in-limit`{.Agda}), which
the kept rud-into-`L` half reads as an asset. The old fragment machinery, the
stage bounding and the discharge served the same-index `defStage∈J`, which
the bridge records as false; the corrected successor statement is
`BlockPowLim`{.Agda} in the SatTable chapter, one ω-block up, and the
discharge of its one hypothesis happens there.
<!--zh-->
本章的两条存续事实是后继坍缩 (`Lsuc≡Def`{.Agda})，它把后继陈述转成关于可定义幂的陈述，以及极限处的包含那一半 (`defs-in-limit`{.Agda})，被保留的初步函数进 `L` 那一半把它当作资产来读。旧的片段机器、阶段定界与兑付都服务于同索引的 `defStage∈J`，而桥已把它记作假命题；修正后的后继陈述是 SatTable 章中的 `BlockPowLim`{.Agda}，整体高出一个 ω 块，其唯一假设的兑付在那里完成。
<!--/-->
