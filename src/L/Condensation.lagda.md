# The condensation crossing

<!--en-->
The condensation lemma is the recognition step of constructibility theory.
Devlin states it for an elementary substructure of a level: the substructure
collapses onto a unique transitive set, and the lemma identifies the collapsed
set as a level of the real tower ([dev2.txt:1148]). The collapse half is the
subject of its own probe, green and carrier-neutral; the elementary-substructure
half, the hull, is separately priced. This chapter is the crossing, the
recognition half, and it is the third consumer of the initial-segment face:
where the first consumer wrote the tower story at the real tower, the crossing
reads it at a transitive set carrier `M`, and crosses from that inner reading
to the tower itself.

The chapter delivers the three pieces the condensation probe measured. The
statement layer states the level-hood sentence at a transitive set carrier: the
absoluteness framework instantiates at `M` exactly as it does at the class `L`,
one line for the whole apparatus, and the sentence "the inner world at `M`
assigns the value `v` at the ordinal index `b`" is written once, generic in the
formula. The successor case proves, from `M`'s internal story and one crossing
hypothesis, that every definable subset of a level indexed inside `M` is
already a member of `M`, that every level indexed inside `M` is a member of
`M`, and that `M` is contained in `L`. The crossing itself is reduced to its
measured residue: one absoluteness obligation about one formula, at the two
carriers, with the reduction proved and the obligation stated, priced, and left
standing.
<!--zh-->
凝聚引理是可构造性理论中的识别一步。Devlin 把它陈述在某个层的初等子结构上：该子结构坍缩到唯一的传递集上，而引理把坍缩所得识别为真实塔的一层 ([dev2.txt:1148])。坍缩半边由它自己的探针测量，绿灯且与载体无关；初等子结构半边，即外壳，另行定价。本章是跨越，即识别半边，也是初始段面孔的第三个消费方：第一个消费方在真实塔处写下塔故事，而跨越在传递集载体 `M` 处读它，并从那条内层读式跨向塔本身。

本章交付凝聚探针测得的三个部件。陈述层在传递集载体处陈述层句：绝对性框架在 `M` 处的实例化与在类 `L` 处一字不差，整台机器一行到位，而句子「`M` 的内层世界在序数指标 `b` 处指派值 `v`」一次写成、以公式为参数。后继情形从 `M` 的内部故事与一条跨越假设出发，证明：指标落在 `M` 内的每一层，其每个可定义子集都已经是 `M` 的成员；指标落在 `M` 内的每一层都是 `M` 的成员；且 `M` 含于 `L`。跨越本身被化归到它测得的残余：关于一条公式、在两个载体处的一条绝对性义务，化归得证，义务被陈述、定价并留待后继。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Condensation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using
  ( isL; isL-trans; isTransV; IsOrd; 𝒟ₒ; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )

open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open hPropStructure 𝒮ᵥ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At S (λ x → x) using () renaming ( _⊨_ to _⊨ⱽ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

-- The constructible sets, as the absoluteness chapter names them.
Sʟ : Type (ℓ-suc ℓ)
Sʟ = AbsL.SM

-- Every ordinal is constructible: it appears at the stage after itself, and
-- that stage is a level.  Both factors are delivered; the combination is not
-- exported anywhere, so it is re-derived here in one line.
ord-isL : (a : S) → IsOrd a → ⟨ isL a ⟩
ord-isL a oa = Lset→isL (sucV a) (suc-ord oa) a (ord∈Lset-suc a oa)
```

<!--en-->
## The set carrier
<!--zh-->
## 集合载体
<!--/-->

<!--en-->
The absoluteness chapter's machine is generic in the restriction class, and a
transitive set is a restriction class in its own right: `isTransV M` is
definitionally the transitivity witness the machine asks for, so the whole
apparatus, the inner world `SM`, the two satisfactions `⊨ᵐ` and `⊨ᵛ`, and the
transfers `abs₀`, `σ₁-up`, `π₁-down`, instantiate at `∈ˢ M` in one line. The
set carrier is the crossing's working face, exactly as the class carrier was
the hierarchy chapter's.

The level formula lives at the class carrier, so the carrier section also
names the two maps the crossing moves along: `Sʟ`, the constructible sets as
the absoluteness chapter names them at `L`, and `InM`, the membership of a
constructible set's carrier value in `M`. One small fact is re-derived here
because the tree does not export it: every ordinal is constructible, since it
appears at the stage after itself and that stage is a level.
<!--zh-->
绝对性章的机器以限制类为参数，而传递集本身就是限制类：`isTransV M` 定义性地就是机器所索要的传递性见证，于是整台机器，内层世界 `SM`、两套满足 `⊨ᵐ` 与 `⊨ᵛ`，以及转移 `abs₀`、`σ₁-up`、`π₁-down`，在 `∈ˢ M` 处一行实例化。集合载体是跨越的工作面，正如类载体是层级章的工作面。

层公式住在类载体处，故载体一节也点名跨越沿之移动的两条映射：`Sʟ`，即绝对性章在 `L` 处命名的可构造集，以及 `InM`，即某个可构造集的载体值对 `M` 的隶属。此处还重新推导了一条树中未导出的小事实：每个序数都可构造，因为它现身于自身之后的那个阶段，而那个阶段是一层。
<!--/-->

```agda
module AtCarrier (M : S) (Mtr : isTransV M) where

  -- The set carrier is a first-class restriction class: the whole
  -- absoluteness apparatus instantiates at `∈ˢ M` in one line.
  module AbsM = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ M) Mtr

  Sᴹ : Type (ℓ-suc ℓ)
  Sᴹ = AbsM.SM

  InM : Sʟ → Type (ℓ-suc ℓ)
  InM c = ⟨ fst c ∈ˢ M ⟩

  -- The certified relabelling moves the level formula from the class carrier
  -- down to the set carrier, one constant at a time.
  module Down = Relabel {K = Sʟ} {K' = Sᴹ} {W = S}
                  fst fst InM (λ c p → fst c , p) (λ c p → refl)
```

<!--en-->
## The level-hood sentence at the carrier
<!--zh-->
## 载体处的层句
<!--/-->

<!--en-->
With the carrier in place, the level-hood sentence is stated once, generic in
the formula. `Believes φ v b` is the inner reading at `M`: the formula holds
with the value at variable zero and the index at variable one. `CrossOut φ` is
the crossing obligation itself: whenever the inner world believes the formula
at an ordinal index, the value named IS the tower's level at that index. The
rest of the face at the carrier names what the condensation induction consumes:
`HasLevels φ` (every ordinal index in `M` has a believed value), `Covered φ`
(every member of `M` lies in a believed value), `SucClosed` (`M` closed under
the ordinal successor, the fragment of `M`'s internal set theory the successor
case needs), and `Condenses`, the target statement, "`M` is a level".
<!--zh-->
载体就位后，层句一次写成、以公式为参数。`Believes φ v b` 是 `M` 处的内层读式：公式以值在变量零、指标在变量一处成立。`CrossOut φ` 就是跨越义务本身：凡内层世界在某个序数指标处相信该公式，被点名的值就**是**塔在该指标处的层。载体处面孔的其余部分点名凝聚归纳所消费的条目：`HasLevels φ` (`M` 中每个序数指标都有被相信的值)、`Covered φ` (`M` 的每个成员都落在某个被相信的值里)、`SucClosed` (`M` 对序数后继封闭，这是后继情形所需的 `M` 内部集合论片段)，以及目标陈述 `Condenses`，即「`M` 是一层」。
<!--/-->

```agda
  Believes : Formula Sᴹ 2 → Sᴹ → Sᴹ → Type (ℓ-suc ℓ)
  Believes φ v b = ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩

  -- The crossing: a believed value at an ordinal index is the tower's level
  -- there.
  CrossOut : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b
             → fst v ≡ Lset (fst b)

  -- M's internal story, three clauses.
  HasLevels : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  HasLevels φ = (b : Sᴹ) → IsOrd (fst b)
              → ∥ Σ[ v ∈ Sᴹ ] Believes φ v b ∥₁

  Covered : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  Covered φ = (x : Sᴹ)
            → ∥ Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
                (IsOrd (fst b) × Believes φ v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁

  SucClosed : Type (ℓ-suc ℓ)
  SucClosed = (b : Sᴹ) → IsOrd (fst b) → ⟨ sucV (fst b) ∈ˢ M ⟩

  -- The target: M is a level of the real tower.
  Condenses : Type (ℓ-suc ℓ)
  Condenses = Σ[ β ∈ S ] (IsOrd β × (M ≡ Lset β))
```

<!--en-->
## The successor case
<!--zh-->
## 后继情形
<!--/-->

<!--en-->
The successor clause of the condensation induction says the collapsed image of
a stage is a stage. Over the delivered tower that is `Lset-suc`, one equation:
the stage after `δ` is the definable power of the stage at `δ`. If `M`'s
internal story supplies a level at `sucV δ`, the crossing names that level, and
the equation rewrites it to `𝒟ₒ (Lset δ)`; transitivity of `M` then brings
every definable subset of the `δ`-th level inside `M`.
<!--zh-->
凝聚归纳的后继子句说：一个阶段的坍缩像仍是一个阶段。在已交付的塔上，这就是 `Lset-suc` 一条方程：`δ` 之后的阶段是 `δ` 处阶段的可定义幂。若 `M` 的内部故事在 `sucV δ` 处供给一层，跨越就点名那一层，方程把它改写成 `𝒟ₒ (Lset δ)`；`M` 的传递性随之把第 `δ` 层的每个可定义子集都带进 `M`。
<!--/-->

```agda
  module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ) where

    succ-step : HasLevels φ → SucClosed
              → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ
              → (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩ → ⟨ x ∈ˢ M ⟩
    succ-step hl sc δ δ∈ oδ x x∈ =
      PT.rec (snd (x ∈ˢ M)) go (hl b (suc-ord oδ))
      where
      b : Sᴹ
      b = sucV δ , sc (δ , δ∈) oδ
      go : Σ[ v ∈ Sᴹ ] Believes φ v b → ⟨ x ∈ˢ M ⟩
      go (v , hv) = Mtr {x = fst v} {y = x}
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym q) x∈) (snd v)
        where
        q : fst v ≡ 𝒟ₒ (Lset δ)
        q = co v b (suc-ord oδ) hv ∙ Lset-suc δ
```

<!--en-->
The companion facts are the other two halves of the assembly. Every level
indexed inside `M` is a member of `M`: `M`'s story supplies a believed value at
the index, the crossing names it as `Lset δ`, and the value's own membership
certificate carries the level in. And `M` is contained in `L`: coverage places
every member of `M` in a believed value, the crossing names that value as a
level, and `Lset→isL` hands the constructibility witness. This last is the half
the GCH endgame consumes: a member of `M` is a member of `L`, and once `M` is a
level, a member of `M` is a member of that level.
<!--zh-->
两条伴生事实是装配的另一半。指标落在 `M` 内的每一层都是 `M` 的成员：`M` 的故事在指标处供给一个被相信的值，跨越把它点名为 `Lset δ`，而值自身的隶属证书把层带进来。且 `M` 含于 `L`：覆盖把 `M` 的每个成员放进某个被相信的值，跨越把该值点名为一层，`Lset→isL` 交出可构造性见证。最后这一半正是 GCH 终局所消费的：`M` 的成员是 `L` 的成员，而一旦 `M` 是一层，`M` 的成员就是那一层的成员。
<!--/-->

```agda
    level-in : HasLevels φ
             → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ Lset δ ∈ˢ M ⟩
    level-in hl δ δ∈ oδ =
      PT.rec (snd (Lset δ ∈ˢ M)) go (hl (δ , δ∈) oδ)
      where
      go : Σ[ v ∈ Sᴹ ] Believes φ v (δ , δ∈) → ⟨ Lset δ ∈ˢ M ⟩
      go (v , hv) =
        subst (λ w → ⟨ w ∈ˢ M ⟩) (co v (δ , δ∈) oδ hv) (snd v)

    M⊆L : Covered φ → (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ isL x ⟩
    M⊆L cv x x∈ = PT.rec (snd (isL x)) go (cv (x , x∈))
      where
      go : Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
             (IsOrd (fst b) × Believes φ v b × ⟨ x ∈ˢ fst v ⟩)
         → ⟨ isL x ⟩
      go (b , v , ob , hv , x∈v) = Lset→isL (fst b) ob x
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (co v b ob hv) x∈v)
```

<!--en-->
## The transport is meaning-preserving
<!--zh-->
## 迁移保义
<!--/-->

<!--en-->
The crossing needs the level formula at the set carrier, and the formula lives
at the class carrier. The certified relabelling of the bounding chapter moves
it down, occurrence by occurrence, against a per-constant certificate, and the
move changes nothing that matters: read ambiently, the transported formula
means exactly the original. The agreement is proved here generically in the
formula, so no closed sentence is ever normalized, and the transport never has
to be fought at the crossing site.
<!--zh-->
跨越需要层公式落在集合载体处，而公式住在类载体处。有界章的经证书重标把公式逐次出现地向下迁移，逐常元对照一份证书，而这次迁移没有改变任何要紧的东西：环境读之下，被迁移的公式与原式意思完全一致。此处对公式泛型地证明这条一致，于是没有任何闭句被正规化，跨越现场也不必与迁移搏斗。
<!--/-->

```agda
  module Transport (Φ : Formula Sʟ 2) (h : BoundedFo InM Φ) where

    lifted : Formula Sᴹ 2
    lifted = Down.liftFo Φ h

    amb-agree : (γ : S ^ 2) → (γ AbsM.⊨ᵛ lifted) ≡ (γ AbsL.⊨ᵛ Φ)
    amb-agree γ =
        sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst (λ x → x) lifted γ)
      ∙ cong (λ ψ → γ ⊨ⱽ ψ) (Down.liftFo-correct Φ h)
      ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst (λ x → x) Φ γ

  -- The transfer the crossing needs at M: the inner reading implies the
  -- ambient reading of the transported formula.
  TransferM : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  TransferM φ = (v b : Sᴹ) → ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩
              → ⟨ (fst v ∷ fst b ∷ []) AbsM.⊨ᵛ φ ⟩
```

<!--en-->
## The crossing, reduced
<!--zh-->
## 跨越，化归之后
<!--/-->

<!--en-->
The crossing obligation is one absoluteness theorem about one formula at two
carriers. At the set carrier it needs `TransferM`: the inner reading implies
the ambient reading of the transported formula, what `σ₁-up` would give. At the
class carrier it needs the ambient-reading form of the hierarchy chapter's
`Lset-only`: the delivered theorem is stated at the inner reading only, so the
ambient form is a second, undelivered obligation, and it factors into exactly
two pieces: `TransferL`, the ambient reading implies the inner reading at `L`,
what `π₁-down` would give, and `ValueIsL`, the value named by an ambient
satisfaction is constructible. The factorization is proved here, and the whole
crossing assembles from the two transfers: at a transitive set carrier, the
inner face crosses out through one transfer at `M` and the ambient form at `L`.
<!--zh-->
跨越义务是关于一条公式、在两个载体处的一条绝对性定理。在集合载体处它需要 `TransferM`：内层读式蕴含被迁移公式的环境读式，即 `σ₁-up` 会给出的东西。在类载体处它需要层级章 `Lset-only` 的环境读式形态：已交付的定理只陈述在内层读式处，故环境形态是第二条未交付的义务，而它恰好分解成两件：`TransferL`，环境读式蕴含 `L` 处的内层读式，即 `π₁-down` 会给出的东西，以及 `ValueIsL`，被环境满足点名的值可构造。分解在此得证，而整条跨越从两条转移装配：在传递集载体处，内层面孔经 `M` 处的一条转移与 `L` 处的环境形态跨出去。
<!--/-->

```agda
-- The ambient-reading form of `Lset-only`, at the class carrier.  The
-- delivered theorem is stated at the inner reading only.
AmbientOnly : Type (ℓ-suc ℓ)
AmbientOnly = (v b : S) → IsOrd b
            → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
            → v ≡ Lset b

TransferL : Type (ℓ-suc ℓ)
TransferL = (v b : Sʟ)
          → ⟨ (fst v ∷ fst b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
          → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt {2} zero (suc zero) ⟩

ValueIsL : Type (ℓ-suc ℓ)
ValueIsL = (v b : S) → IsOrd b
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
         → ⟨ isL v ⟩

-- The ambient form factors into the transfer at L and the value's
-- constructibility.
ambientOnly-from : TransferL → ValueIsL → AmbientOnly
ambientOnly-from tl vl v b ob h =
  Lset-only zero (suc zero) (vL ∷ bL ∷ []) (tl vL bL h) ob
  where
  bL : Sʟ
  bL = b , ord-isL b ob
  vL : Sʟ
  vL = v , vl v b ob h

-- The crossing, assembled: at a transitive set carrier, one transfer at M and
-- the ambient form at L give the crossing obligation for the level formula.
module Crossing (M : S) (Mtr : isTransV M)
                (h : BoundedFo (AtCarrier.InM M Mtr)
                       (LsetGraphAt {2} zero (suc zero))) where

  open AtCarrier M Mtr
  open Transport (LsetGraphAt {2} zero (suc zero)) h

  crossOut-from : TransferM lifted → AmbientOnly → CrossOut lifted
  crossOut-from tm ao v b ob hv =
    ao (fst v) (fst b) ob
      (subst ⟨_⟩ (amb-agree (fst v ∷ fst b ∷ [])) (tm v b hv))
```

<!--en-->
Neither `TransferM` nor `AmbientOnly` is delivered, and the probe measured why,
machine-checked: the level formula is neither Δ₀, Σ₁, nor Π₁ in the delivered
certification, since its quantifier profile carries unbounded quantifiers of
both kinds, so none of the three delivered transfer theorems applies. Producing
the Levy form of the formula is the priced residue, and this chapter stops
there, stating the obligation and the reduction. The limit case is stated as
the target `Condenses` but not built: it needs the ordinal predicate at the set
carrier, which the ordinal chapter ships carrier-generic and Δ₀-certified, and
the two inclusions, `M ⊆ L` (delivered above) and the reverse from `level-in`
plus one extensionality, priced in the report and left standing.
<!--zh-->
`TransferM` 与 `AmbientOnly` 都未交付，而探针机检地量到了原因：层公式在已交付的证书体系中既非 Δ₀、亦非 Σ₁、亦非 Π₁，因为它的量词画像同时携带两种无界量词，于是三条已交付的转移定理没有一条适用。造出公式的 Lévy 形态就是那条被定价的残余，本章在此停下，陈述义务与化归。极限情形被陈述为目标 `Condenses` 而未建造：它需要集合载体处的序数谓词，序数章以载体为参数、带 Δ₀ 证书地交付了它，还需要两条包含，`M ⊆ L` (上文已交付) 与由 `level-in` 加一次外延性得出的反向，在报告中定价并留待后继。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the condensation crossing's measured core: the level-hood
sentence at a transitive set carrier, the successor case with its two
companions, the meaning-preserving transport, and the crossing reduced to one
absoluteness obligation about one formula at the two carriers, with the
factorization proved. What remains is the obligation itself, the Levy content
of the level formula, plus the limit case; the collapse half is separately
probed green and the hull separately priced. The crossing is the face's third
consumer, and the orchestrator wires this chapter into `Everything`.
<!--zh-->
本章交付凝聚跨越的测得核心：传递集载体处的层句、后继情形及其两条伴生事实、保义的迁移，以及化归为「关于一条公式、在两个载体处的一条绝对性义务」的跨越，分解得证。所余的是义务本身，即层公式的 Lévy 内容，连同极限情形；坍缩半边另有探针测得绿灯，外壳另有定价。跨越是面孔的第三个消费方，编排者把本章接入 `Everything`。
<!--/-->
