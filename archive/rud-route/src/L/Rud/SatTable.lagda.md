# The definable power as the image of a table

<!--en-->
The bridge's successor step is one set: the totality of the definable subsets
of a constructible stage, asked to be a member of the next ω-block above the
level that holds the stage. This chapter says what shape that set has, closes
the shape into the corrected block statement, and names the one hypothesis
the step still needs.

The shape is the classical one. A satisfaction relation over a carrier is a
set of pairs, a code with a member the coded formula selects; slicing it at
one code returns that formula's definable set, and collecting the slices over
a covering set returns the definable power. Both operations are in the rud
basis, the slice as the tenth and the collection as the eighth, so a level
that holds the relation and the covering set holds the definable power
outright, with no offset at all. The identity is proved at an arbitrary code
map, so that no choice of coding is baked into it.

The corrected successor statement is the one-block form: at a limit level
holding the stage, the definable power lands one ω-block up. The same-index
form is false, recorded as such in the bridge (Devlin VI.2.4), and the older
index machinery that ran on the first-limit split is gone with it. What
remains as the step's single hypothesis is the re-stated relation: a member
of the next block whose slices over a covering set collect the definable
power, with the covering set itself a member too. One hypothesis away is the
reading this chapter delivers.
<!--zh-->
桥的后继步是一个集合：某可构造阶段的全体可定义子集，被要求成为持有该阶段的那一层之上下一个 ω 块的成员。本章说清该集合是什么形状，把这个形状封成修正后的块陈述，并点名这一步仍缺的那一条假设。

形状是经典的那个。载体之上的一条满足关系是一个对之集，即一条码配上该码所指公式选中的一个成员；在单条码处切片，取回那条公式的可定义集，而在一个覆盖集上收拢诸切片，取回可定义幂。两个运算都在初步基底之内，切片是第十个、收拢是第八个，故同时持有该关系与该覆盖集的层直接持有可定义幂，一点偏移也不用。恒等式在任意码映射上证出，好让任何编码选择都不被烙进来。

修正后的后继陈述是单块形：在持有该阶段的极限层处，可定义幂落在高出一个
ω 块之处。同索引形是假的，已在桥中如实记下 (Devlin VI.2.4)，而旧的那套依第一个极限切分的索引机器随之一并消失。这一步唯一剩下的假设是重述后的关系：下一个块的一个成员，其在某个覆盖集上的诸切片收拢出可定义幂，覆盖集自身亦为该块的成员。只差这一条假设，本章即给出那个读出。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.SatTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rud.Images {ℓ} using ( F8; F8-spec; F10 )
open import L.Rud.Step {ℓ} lem A using ( f8; Fof-f8; Sset; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord; isLimit-not-zero )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit )
open import L.Rud.DefInJ {ℓ} lem A using ( Lsuc≡Def )
open import L.Rud.Bridge {ℓ} lem A using ( ∅∈Lset )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The slice and the collection
<!--zh-->
## 切片与收拢
<!--/-->

<!--en-->
The definable power is one collection of one relation's slices, and the whole
identity is stated at an abstract code map. A code map assigns a set to each
formula over the carrier; a set **covers** the map when it holds every code
and holds nothing else; and a relation **slices** to the map when its slice
at a formula's code is that formula's definable set. Under those two, the
collection of the relation's slices over the covering set is the definable
power on the nose.

Nothing about the coding is used, and that is deliberate: the identity is the
part of this chapter that survives a change of coding.
<!--zh-->
可定义幂就是某一条关系的诸切片的一次收拢，而整条恒等式是在抽象的码映射上陈述的。码映射把载体之上的每条公式指派到一个集合；一个集合**覆盖**该映射，当它持有每条码且不持有别的东西；而一条关系**切合**该映射，当它在某条公式之码处的切片就是该公式的可定义集。在这两条之下，该关系在覆盖集上诸切片的收拢，恰好就是可定义幂。

编码的任何细节都没有被用到，而这是有意为之：这条恒等式是本章中经得起编码更换的那一部分。
<!--/-->

```agda
private
  ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
        → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
  ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

module Pow (C : S) where

  open DefOf C using ( defSet )

  Cod : Type (ℓ-suc ℓ)
  Cod = Formula ⟪ C ⟫ 1 → S

  Covers : S → Cod → Type (ℓ-suc ℓ)
  Covers K cod =
      ((φ : Formula ⟪ C ⟫ 1) → ⟨ cod φ ∈ˢ K ⟩)
    × ((c : S) → ⟨ c ∈ˢ K ⟩ → ∥ Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (cod φ ≡ c) ∥₁)

  Slices : S → Cod → Type (ℓ-suc ℓ)
  Slices R cod = (φ : Formula ⟪ C ⟫ 1) → F10 R (cod φ) ≡ defSet φ

  pow≡ : (K R : S) (cod : Cod) → Covers K cod → Slices R cod → F8 R K ≡ 𝒟ₒ C
  pow≡ K R cod (into , outof) sl = ext-⊆ sub sup
    where
    sub : (y : S) → ⟨ y ∈ˢ F8 R K ⟩ → ⟨ y ∈ˢ 𝒟ₒ C ⟩
    sub y h = PT.rec (snd (y ∈ˢ 𝒟ₒ C)) atIdx (subst ⟨_⟩ (F8-spec R K y) h)
      where
      atIdx : Σ[ m ∈ ⟪ K ⟫ ] (F10 R (⟪ K ⟫↪ m) ≡ y) → ⟨ y ∈ˢ 𝒟ₒ C ⟩
      atIdx (m , e) = PT.rec (snd (y ∈ˢ 𝒟ₒ C)) atFo
        (outof (⟪ K ⟫↪ m) (∈∈ₛ {a = ⟪ K ⟫↪ m} {b = K} .snd (∈ₛ⟪ K ⟫↪ m)))
        where
        atFo : Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (cod φ ≡ ⟪ K ⟫↪ m) → ⟨ y ∈ˢ 𝒟ₒ C ⟩
        atFo (φ , q) =
          𝒟ₒ-intro C y ∣ φ , (sym (sl φ) ∙ cong (F10 R) q ∙ e) ∣₁
    sup : (y : S) → ⟨ y ∈ˢ 𝒟ₒ C ⟩ → ⟨ y ∈ˢ F8 R K ⟩
    sup y h = PT.rec (snd (y ∈ˢ F8 R K)) atFo (𝒟ₒ-inv C y h)
      where
      atFo : Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (defSet φ ≡ y) → ⟨ y ∈ˢ F8 R K ⟩
      atFo (φ , q) = subst ⟨_⟩ (sym (F8-spec R K y)) ∣ fib .fst , path ∣₁
        where
        fib : Σ[ m ∈ ⟪ K ⟫ ] (⟪ K ⟫↪ m ≡ cod φ)
        fib = ∈-asFiber {a = cod φ} {b = K} (into φ)
        path : F10 R (⟪ K ⟫↪ (fib .fst)) ≡ y
        path = cong (F10 R) (fib .snd) ∙ sl φ ∙ q

  pow∈J : (γ : S) → ⟨ isLimit γ ⟩ → (K R : S) (cod : Cod)
        → Covers K cod → Slices R cod
        → ⟨ K ∈ˢ Sset γ ⟩ → ⟨ R ∈ˢ Sset γ ⟩ → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  pow∈J γ limγ K R cod cov sl hK hR =
    subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f8 R K ∙ pow≡ K R cod cov sl)
      (Jset-rud γ limγ f8 R K hR hK)
```

<!--en-->
## The successor hypothesis, re-stated
<!--zh-->
## 后继假设的重述
<!--/-->

<!--en-->
The step's one hypothesis is the re-stated relation: a member of the level
whose slices over a covering set collect the definable power, with the
covering set itself a member too. It is stated code-free, at an arbitrary
code map, so the coded chapters' own machinery is not part of the statement:
membership and formula-slicing are supplied by the relation and its adequacy,
and the collection identity below turns the hypothesis into the definable
power with no further index work.
<!--zh-->
这一步的唯一假设是重述后的关系：该层的一个成员，其在某个覆盖集上的诸切片收拢出可定义幂，覆盖集自身亦为该层的成员。它无编码地陈述、落在任意码映射上，故编码诸章自己的机器不在这条陈述之内：隶属与公式切片由该关系及其
adequacy 供给，而下面的收拢恒等式无需任何进一步的索引工作，就把假设变成可定义幂。
<!--/-->

```agda
module Coded (γ : S) (limγ : ⟨ isLimit γ ⟩) (C : S) where

  open Pow C using ( Cod; Covers; Slices; pow∈J )

  SatRelation : S → Type (ℓ-suc ℓ)
  SatRelation R = ⟨ R ∈ˢ Sset γ ⟩
                × (Σ[ K ∈ S ] (Σ[ cod ∈ Cod ]
                    (⟨ K ∈ˢ Sset γ ⟩ × Covers K cod × Slices R cod)))

  coded-pow : (R : S) → SatRelation R → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  coded-pow R (hR , K , cod , hK , cov , sl) =
    pow∈J γ limγ K R cod cov sl hK hR
```

<!--en-->
## The block power at a limit
<!--zh-->
## 极限处的块幂
<!--/-->

<!--en-->
The corrected target is the one-block form: at a limit level holding the
stage, the definable power is a member of the next ω-block. The original
`BlockPow`{.Agda} without the limit hypothesis is stronger than the
literature and unreachable through any coding (D-10's correction, Devlin
VI.2.3), and the derivation of the old ∀-over-limits form from the block
form is refuted at the one-block boundary; both are gone. What is delivered
is the discharge of the corrected target from the re-stated relation: the
pair `(δ, +ω δ)` is the successor step's own pair, the outer level is a limit
by construction and holds the carrier by one membership step, and the
collection identity places the definable power in it. The successor collapse
then reads the same membership at the successor stage.
<!--zh-->
修正后的目标是单块形：在持有该阶段的极限层处，可定义幂是下一个 ω 块的成员。没有极限假设的原 `BlockPow`{.Agda} 强于文献、且没有任何编码够得到它
(D-10 的修正，Devlin VI.2.3)，而从块形推出旧的全极限形在单块边界处被反驳；二者都已不在。此处交付的是从重述后的关系兑付修正后的目标：对 `(δ, +ω
δ)` 正是后继步自己的那对层，外层按构造是极限并经一步隶属持有载体，收拢恒等式把可定义幂放进去。后继坍缩随即把同一隶属读在后继阶段处。
<!--/-->

```agda
BlockPowLim : Type (ℓ-suc ℓ)
BlockPowLim = (ζ δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
            → ⟨ Lset ζ ∈ˢ Sset δ ⟩ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ) ⟩

blockPow-at-limit : (δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
                  → (C : S) → (C∈ : ⟨ C ∈ˢ Sset δ ⟩) → (R : S)
                  → Coded.SatRelation (+ω δ) (+ω-limit δ ordδ) C R
                  → ⟨ 𝒟ₒ C ∈ˢ Sset (+ω δ) ⟩
blockPow-at-limit δ ordδ limδ C C∈ R sr =
  Coded.coded-pow (+ω δ) (+ω-limit δ ordδ) C R sr

blockPow-suc : (δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
             → (ζ : S) → (L∈ : ⟨ Lset ζ ∈ˢ Sset δ ⟩) → (R : S)
             → Coded.SatRelation (+ω δ) (+ω-limit δ ordδ) (Lset ζ) R
             → ⟨ Lset (sucV ζ) ∈ˢ Sset (+ω δ) ⟩
blockPow-suc δ ordδ limδ ζ L∈ R sr =
  subst (λ w → ⟨ w ∈ˢ Sset (+ω δ) ⟩) (sym (Lsuc≡Def ζ))
    (blockPow-at-limit δ ordδ limδ (Lset ζ) L∈ R sr)
```

<!--en-->
## The relativization slot at the trunk
<!--zh-->
## 主干处的相对化槽
<!--/-->

<!--en-->
The kept rud-into-`L` half of the bridge reads its relativization slot at the
plain trunk, where the slot is the empty set. Every limit holds the empty
set, which reads directly from the ordinal trichotomy against `∅`; the old
comparison against the first limit, which carried the first-limit split, is
gone with it.
<!--zh-->
被保留的初步函数进 `L` 那一半，在非相对化主干处读它的相对化槽，那里的槽正是空集。每个极限都持有空集，这直接由对着 `∅` 的序数三歧读出；旧的对第一个极限的比较，连同它承载的第一个极限切分，一并消失。
<!--/-->

```agda
∅∈limit : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ ∅ ∈ˢ γ ⟩
∅∈limit γ limγ = pick (ord-tri ∅ ∅-ord γ (isLimit-ord γ limγ))
  where
  pick : ⟨ ∅ ∈ˢ γ ⟩ ⊎ ((∅ ≡ γ) ⊎ ⟨ γ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ γ ⟩
  pick (inl h) = h
  pick (inr (inl e)) = Empty.rec (isLimit-not-zero γ limγ (sym e))
  pick (inr (inr h)) = Empty.rec (∅-empty γ (∈∈ₛ {a = γ} {b = ∅} .fst h))

slot-empty : A ≡ ∅ → (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩
slot-empty e γ limγ = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym e)
  (∅∈Lset γ limγ (∅∈limit γ limγ))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The definable power of a carrier is the eighth basis operation applied to a
relation and a set covering the codes (`pow≡`{.Agda}, `pow∈J`{.Agda}), so a
level holding both holds the definable power with no offset. The successor
step's one hypothesis is the re-stated relation (`SatRelation`{.Agda},
`coded-pow`{.Agda}), stated code-free with its membership and slicing carried
as the relation's own content. The corrected block statement
(`BlockPowLim`{.Agda}) is discharged from it at the step's own pair
(`blockPow-at-limit`{.Agda}), and read at the successor stage
(`blockPow-suc`{.Agda}); the trunk's relativization slot is the empty set at
every limit (`∅∈limit`{.Agda}, `slot-empty`{.Agda}). The full bridge
instantiation is the reshaped reduction's consumer, which the bridge chapter
owns; this chapter delivers the successor step's supplies and stops there.
<!--zh-->
载体的可定义幂是第八个基底运算施于一条关系与一个覆盖诸码的集合之值
(`pow≡`{.Agda}、`pow∈J`{.Agda})，故同时持有二者的层不带任何偏移地持有可定义幂。后继步的唯一假设是重述后的关系 (`SatRelation`{.Agda}、`coded-pow`{.Agda})，无编码地陈述，隶属与切片作为该关系自身的内容携带。修正后的块陈述 (`BlockPowLim`{.Agda}) 在该步自己的那对层处由它兑付
(`blockPow-at-limit`{.Agda})，并在后继阶段处读出 (`blockPow-suc`{.Agda})；主干处的相对化槽在每个极限处都是空集 (`∅∈limit`{.Agda}、`slot-empty`{.Agda})。整座桥的实例化是重塑后归约的消费方，归桥那一章所有；本章交付后继步的诸供应，并止步于此。
<!--/-->
