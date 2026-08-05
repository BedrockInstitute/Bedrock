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
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map; mapFo; mapΔ₀; embed )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀; π-∀ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using
  ( isL; isL-trans; isTransV; IsOrd; 𝒟ₒ; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )

open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( map )
import Cubical.Data.Empty as Empty
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
## The level story at the set carrier
<!--zh-->
## 集合载体处的层故事
<!--/-->

<!--en-->
The crossing reads the level story at the set carrier, and the story now
lives there in its Levy form. This section transports the six measured
clauses, the collapsed Def-step entry and the range read down to `Sᴹ`,
assembles them into one Sigma-1 formula, and certifies the two readings the
crossing distinguishes: the inner reading in `𝒮 ↾ M` and the ambient reading
in `𝒮`. The transport is the relabelling kit: the story is written once on
the parameter-free axis, where it carries no constants, and `embed`{.Agda}
moves it to any constant domain, with `mapΔ₀`{.Agda} and the Sigma-1
transport carrying the witnesses. No carrier fact about `Sᴹ` enters: the
story never mentions a constant, and the witness `f` ranges over `Sᴹ` by the
type, never by a formula bound (the D-16 working face).
<!--zh-->
跨越在集合载体处读层故事，而故事如今也以 Lévy 形态住在那里。本节把六条测得子句、坍缩后的 Def 步条目与像读式迁移到 `Sᴹ`，装配成一条 Σ₁ 公式，并认证跨越所区分的两条读式：`𝒮 ↾ M` 中的内层读式与 `𝒮` 中的环境读式。迁移借助重标工具组：故事在无参轴上只写一次，那里它不带任何常元，`embed`{.Agda} 把它送到任意常量域，`mapΔ₀`{.Agda} 与 Σ₁ 运输携带见证。`Sᴹ` 的载体事实一项也未进入：故事从不点名常元，见证 `f` 以类型、而非公式绑定，被携带在 `Sᴹ` 上 (D-16 工作面)。
<!--/-->

<!--en-->
The story is told with structural predicates, each bounded and each carrying
its Delta-0 witness: singletons, unordered pairs of two distinct sets,
Kuratowski pairs, the first-component relations, and the ordinal,
limit-ordinal and limit-of predicates, the shapes the level story's clauses
quantify over. Written once at the empty constant domain `⊥*`, they carry no
constants, so they mean the same at every carrier.
<!--zh-->
故事用一组结构谓词讲出，每条都有界、各带 Δ₀ 见证：单点集、两个相异集合的无序对、库拉托夫斯基对、首分量诸关系，以及序数、极限序数与「首分量为极限序数」诸谓词，正是层故事各子句所量化的形状。它们在空常量域 `⊥*` 处只写一次；因不带常元，它们在每一载体处意思相同。
<!--/-->

```agda
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero

  -- "var k is a singleton": inhabited, all members equal.
  sgl : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  sgl k = ∃̇∈ (var k) (∀̇∈ (var (suc k)) (var f0 ≐ var (suc zero)))

  sglΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (sgl k)
  sglΔ₀ k = δ-∃∈ (δ-∀∈ δ-≐)

  -- "var k is an unordered pair of two distinct sets".
  pair2 : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  pair2 k = ∃̇∈ (var k) (∃̇∈ (var (suc k))
             ( ¬̇ (var f0 ≐ var (suc zero))
             ∧̇ ∀̇∈ (var (suc (suc k)))
                  ((var f0 ≐ var (suc zero)) ∨̇ (var f0 ≐ var (suc (suc zero))))))

  pair2Δ₀ : {n : ℕ} (k : Fin n) → Δ₀ (pair2 k)
  pair2Δ₀ k = δ-∃∈ (δ-∃∈ (δ-∧ (δ-¬ δ-≐) (δ-∀∈ (δ-∨ δ-≐ δ-≐))))

  -- "var k is a Kuratowski pair", degenerate pairs allowed: a singleton
  -- member x; every other member is a two-element set containing x's
  -- element; at most two members.
  kpair : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  kpair k = ∃̇∈ (var k)
             ( sgl f0
             ∧̇ ∀̇∈ (var (suc k))
                  ((var f0 ≐ var (suc zero))
                ∨̇ (pair2 f0 ∧̇ ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero))))
             ∧̇ ∀̇∈ (var (suc k)) (∀̇∈ (var (suc (suc k))) (∀̇∈ (var (suc (suc (suc k))))
                  ((var (suc zero) ≐ var (suc (suc zero)))
                ∨̇ (var f0 ≐ var (suc (suc zero)))
                ∨̇ (var f0 ≐ var (suc zero))))))

  kpairΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (kpair k)
  kpairΔ₀ k = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                 (δ-∧ (δ-∀∈ (δ-∨ δ-≐ (δ-∧ (pair2Δ₀ f0) (δ-∀∈ δ-∈))))
                      (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∨ δ-≐ (δ-∨ δ-≐ δ-≐)))))))

  -- "the first component of var k equals var a" (var k a Kuratowski pair).
  fstEqTo : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ}) n
  fstEqTo k a = ∃̇∈ (var k) (sgl f0 ∧̇ ∀̇∈ (var zero) (var f0 ≐ var (suc (suc a))))

  fstEqToΔ₀ : {n : ℕ} (k a : Fin n) → Δ₀ (fstEqTo k a)
  fstEqToΔ₀ k a = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ δ-≐))

  -- "the first component of var k is a member of the first component of
  -- var l" (both Kuratowski pairs).
  fstLt : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ}) n
  fstLt k l = ∃̇∈ (var k) (sgl f0 ∧̇ ∃̇∈ (var (suc l))
               (sgl f0 ∧̇ ∃̇∈ (var zero)
                 (∀̇∈ (var (suc (suc zero))) (var f0 ∈̇ var (suc zero)))))

  fstLtΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (fstLt k l)
  fstLtΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                (δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∃∈ (δ-∀∈ δ-∈)))))

  -- "var k is a member of the second component of var l".
  sndIn : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ}) n
  sndIn ku kw = ∃̇∈ (var kw) (sgl f0 ∧̇
                ∃̇∈ (var (suc kw)) (pair2 f0 ∧̇
                  ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
                  var (suc (suc ku)) ∈̇ var f0 ∧̇
                  ∀̇∈ (var (suc zero)) (¬̇ (var f0 ≐ var (suc (suc (suc ku)))))))

  sndInΔ₀ : {n : ℕ} (ku kw : Fin n) → Δ₀ (sndIn ku kw)
  sndInΔ₀ ku kw = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                  (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
                    (δ-∧ (δ-∀∈ δ-∈) (δ-∧ δ-∈ (δ-∀∈ (δ-¬ δ-≐)))))))

  -- "the second component of var k is a member of the second component of
  -- var l".
  snd∈Snd : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ}) n
  snd∈Snd k l = ∃̇∈ (var k) (sgl f0 ∧̇
                ∃̇∈ (var (suc k)) (pair2 f0 ∧̇
                  ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
                  ∃̇∈ (var zero) (∀̇∈ (var (suc (suc zero))) (¬̇ (var f0 ≐ var (suc zero)))
                                ∧̇ sndIn f0 (suc (suc (suc l))))))

  snd∈SndΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (snd∈Snd k l)
  snd∈SndΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                  (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
                    (δ-∧ (δ-∀∈ δ-∈) (δ-∃∈ (δ-∧ (δ-∀∈ (δ-¬ δ-≐)) (sndInΔ₀ f0 (suc (suc (suc l))))))))))

  -- The ordinal predicate (delivered shape, already bounded).
  isOrdAt : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  isOrdAt k = (∀̇∈ (var k) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc k)))))
            ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

  isOrdAtΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isOrdAt k)
  isOrdAtΔ₀ k = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

  -- The limit-ordinal predicate, bounded: ordinal, nonempty, no greatest.
  isLimitAt : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  isLimitAt k = isOrdAt k ∧̇ (∃̇∈ (var k) ⊤̇)
              ∧̇ (∀̇∈ (var k) (∃̇∈ (var (suc k)) (var (suc zero) ∈̇ var zero)))

  isLimitAtΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isLimitAt k)
  isLimitAtΔ₀ k = δ-∧ (isOrdAtΔ₀ k) (δ-∧ (δ-∃∈ δ-⊤) (δ-∀∈ (δ-∃∈ δ-∈)))

  -- "the first component of var k is a limit ordinal".
  isLimitOf : {n : ℕ} → Fin n → Formula (⊥* {ℓ}) n
  isLimitOf k = ∃̇∈ (var k) (sgl f0 ∧̇ ∀̇∈ (var zero) (isLimitAt f0))

  isLimitOfΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isLimitOf k)
  isLimitOfΔ₀ k = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (isLimitAtΔ₀ f0)))

  -- "the first components of var k and var l are equal" (both pairs).
  fstEq : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ}) n
  fstEq k l = ∃̇∈ (var k) (sgl f0 ∧̇ ∃̇∈ (var (suc l))
              (sgl f0 ∧̇ ∀̇∈ (var (suc zero)) (∀̇∈ (var zero) (var f0 ≐ var (suc zero)))))

  fstEqΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (fstEq k l)
  fstEqΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                (δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-∀∈ δ-≐)))))
```

<!--en-->
Over these predicates the six clauses of the level story close:
`pairForm`, `singleForm`, `zeroForm`, `domForm`, `limitForm` and the range
read `Rg`. Each is bounded throughout and carries its witness. The Def-step
entry `Cl` collapses to `⊤̇` at every carrier, since every set is definable
in itself (`defSet⊤≡A`), so it is the trivial formula, and the level story
is the conjunction of the approximation, the collapsed step and the range
read.
<!--zh-->
在这组谓词之上，层故事的六条子句闭合：`pairForm`、`singleForm`、`zeroForm`、`domForm`、`limitForm` 与像读式 `Rg`。每条都有界、各带见证。Def 步条目 `Cl` 在每一载体处坍缩为 `⊤̇`，因为每个集合都在自身处可定义 (`defSet⊤≡A`)，故它是平凡公式，而层故事就是近似、坍缩步与像读式的合取。
<!--/-->

```agda
  -- (1) pairForm: every member of f is a Kuratowski pair.
  pairForm : Formula (⊥* {ℓ}) 2
  pairForm = ∀̇∈ (var zero) (kpair f0)

  pairFormΔ₀ : Δ₀ pairForm
  pairFormΔ₀ = δ-∀∈ (kpairΔ₀ f0)

  -- (4) domForm: the first components of the pairs of f form an ordinal,
  -- i.e. a transitive set with transitive members.
  domForm : Formula (⊥* {ℓ}) 2
  domForm = (∀̇∈ (var zero) (kpair f0 ⇒̇
               ∀̇∈ (var zero) (sgl f0 ⇒̇
                 ∀̇∈ (var zero) (∀̇∈ (var zero)
                   (∃̇∈ (var (suc (suc (suc (suc zero)))))
                      (kpair f0 ∧̇ fstEqTo f0 (suc (suc (suc zero)))))))))
           ∧̇
             (∀̇∈ (var zero) (kpair f0 ⇒̇
               ∀̇∈ (var zero) (sgl f0 ⇒̇
                 ∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero)
                   (∃̇∈ (var (suc (suc (suc zero)))) (var (suc zero) ∈̇ var zero)))))))

  domFormΔ₀ : Δ₀ domForm
  domFormΔ₀ = δ-∧
    (δ-∀∈ (δ-⇒ (kpairΔ₀ f0)
       (δ-∀∈ (δ-⇒ (sglΔ₀ f0)
         (δ-∀∈ (δ-∀∈ (δ-∃∈ (δ-∧ (kpairΔ₀ f0) (fstEqToΔ₀ f0 (suc (suc (suc zero))))))))))))
    (δ-∀∈ (δ-⇒ (kpairΔ₀ f0)
       (δ-∀∈ (δ-⇒ (sglΔ₀ f0)
         (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∃∈ δ-∈))))))))

  -- (2) singleForm: two pairs of f with equal first components are equal.
  singleForm : Formula (⊥* {ℓ}) 2
  singleForm = ∀̇∈ (var zero) (∀̇∈ (var (suc zero))
                 (fstEq f0 (suc zero) ⇒̇ var (suc zero) ≐ var zero))

  singleFormΔ₀ : Δ₀ singleForm
  singleFormΔ₀ = δ-∀∈ (δ-∀∈ (δ-⇒ (fstEqΔ₀ f0 (suc zero)) δ-≐))

  -- (3) zeroForm: some memberless a has pr a a in f, i.e. f has a member
  -- that is the singleton of a singleton of a memberless set.
  zeroForm : Formula (⊥* {ℓ}) 2
  zeroForm = ∃̇∈ (var zero) (sgl f0 ∧̇ ∀̇∈ (var zero)
                (sgl f0 ∧̇ ∀̇∈ (var zero) (¬̇ (∃̇∈ (var f0) ⊤̇))))

  zeroFormΔ₀ : Δ₀ zeroForm
  zeroFormΔ₀ = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-¬ (δ-∃∈ δ-⊤))))))

  -- (5) limitForm: at a limit point (a, y) of the graph, y is the union of
  -- the values below a, as two inclusions over the pairs of f.
  limIn : Formula (⊥* {ℓ}) 3
  limIn = ∃̇∈ (var zero) (sgl f0 ∧̇
          ∃̇∈ (var zero) (pair2 f0 ∧̇
            ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
            ∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero))) (¬̇ (var f0 ≐ var (suc zero)))
              ⇒̇ ∃̇∈ (var (suc (suc (suc (suc zero)))))
                   (kpair f0 ∧̇ fstLt f0 (suc (suc (suc (suc zero))))
                         ∧̇ sndIn (suc zero) f0))))

  limInΔ₀ : Δ₀ limIn
  limInΔ₀ = δ-∃∈ (δ-∧ (sglΔ₀ f0)
            (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
              (δ-∧ (δ-∀∈ δ-∈)
                  (δ-∀∈ (δ-⇒ (δ-∀∈ (δ-¬ δ-≐))
                    (δ-∃∈ (δ-∧ (kpairΔ₀ f0)
                      (δ-∧ (fstLtΔ₀ f0 (suc (suc (suc (suc zero)))))
                            (sndInΔ₀ (suc zero) f0))))))))))

  limOut : Formula (⊥* {ℓ}) 3
  limOut = ∀̇∈ (var (suc zero)) (kpair f0 ⇒̇ fstLt f0 (suc zero) ⇒̇ snd∈Snd f0 (suc zero))

  limOutΔ₀ : Δ₀ limOut
  limOutΔ₀ = δ-∀∈ (δ-⇒ (kpairΔ₀ f0) (δ-⇒ (fstLtΔ₀ f0 (suc zero)) (snd∈SndΔ₀ f0 (suc zero))))

  limitForm : Formula (⊥* {ℓ}) 2
  limitForm = ∀̇∈ (var zero) (kpair f0 ⇒̇ isLimitOf f0 ⇒̇ (limIn ∧̇ limOut))

  limitFormΔ₀ : Δ₀ limitForm
  limitFormΔ₀ = δ-∀∈ (δ-⇒ (kpairΔ₀ f0) (δ-⇒ (isLimitOfΔ₀ f0) (δ-∧ limInΔ₀ limOutΔ₀)))

  -- (6) rangeForm: the read member x is the second component of a pair of f.
  Rg : Formula (⊥* {ℓ}) 2
  Rg = ∃̇∈ (var zero) (kpair f0 ∧̇ sndIn (suc (suc zero)) f0)

  RgΔ₀ : Δ₀ Rg
  RgΔ₀ = δ-∃∈ (δ-∧ (kpairΔ₀ f0) (sndInΔ₀ (suc (suc zero)) f0))

  -- The approximation, the collapsed Def-step entry and the range read.
  Ap : Formula (⊥* {ℓ}) 2
  Ap = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ domForm ∧̇ limitForm

  ApΔ₀ : Δ₀ Ap
  ApΔ₀ = δ-∧ pairFormΔ₀
           (δ-∧ singleFormΔ₀ (δ-∧ zeroFormΔ₀ (δ-∧ domFormΔ₀ limitFormΔ₀)))

  Cl : Formula (⊥* {ℓ}) 2
  Cl = ⊤̇

  ClΔ₀ : Δ₀ Cl
  ClΔ₀ = δ-⊤

  -- The level story, as one formula of arity two: the witness f at variable
  -- zero, the read member x at variable one.
  levelStory : Formula (⊥* {ℓ}) 2
  levelStory = Ap ∧̇ (Cl ∧̇ Rg)

  levelStoryΔ₀ : Δ₀ levelStory
  levelStoryΔ₀ = δ-∧ ApΔ₀ (δ-∧ ClΔ₀ RgΔ₀)

  levelStoryΣ₁ : Σ₁ levelStory
  levelStoryΣ₁ = σ-Δ₀ levelStoryΔ₀
```

<!--en-->
The story assembles as one Delta-0 formula, hence Sigma-1. At the set carrier
the transported story is `σᴹ`{.Agda}, the parameter-free story embedded at
`Sᴹ`. The witnesses ride the same relabelling: `mapΔ₀`{.Agda} carries the
Delta-0 witness, and the Sigma-1 transport, one clause per constructor as in
the delivered tower transport, carries `Σ₁ σᴹ`{.Agda}. The two readings then
agree on the nose: `abs₀`{.Agda} at the restriction `M` makes the inner
reading equal to the ambient reading of the same formula, spending
transitivity exactly at the bounded quantifiers, and the crossing's
`TransferM` follows by `σ₁-up`{.Agda}.
<!--zh-->
故事装配成一条 Δ₀ 公式，从而是 Σ₁。在集合载体处，被迁移的故事就是把无参故事经 `embed`{.Agda} 送到 `Sᴹ` 所得，名为 `σᴹ`{.Agda}。见证随同一套重标同行：`mapΔ₀`{.Agda} 携带 Δ₀ 见证，而 Σ₁ 运输逐构造子一如已交付的塔运输，携带 `Σ₁ σᴹ`{.Agda}。两条读式于是分毫不差地一致：限制 `M` 处的 `abs₀`{.Agda} 使同一条公式的内层读式等于环境读式，传递性恰在有界量词处被花掉，而跨越的 `TransferM` 由 `σ₁-up`{.Agda} 得出。
<!--/-->

```agda
  -- The Sigma-1 instance of the delivered tower transport: one clause per
  -- constructor, `mapΔ₀` at the Delta-0 leaf.
  mapΣ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        → {n : ℕ} {φ : Formula K n} → Σ₁ φ → Σ₁ (mapFo f φ)
  mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
  mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)

  -- The set-carrier level story: the parameter-free story embedded at Sᴹ.
  σᴹ : Formula Sᴹ 2
  σᴹ = embed levelStory

  -- The two witnesses ride the same relabelling.
  levelΔ₀ : Δ₀ σᴹ
  levelΔ₀ = mapΔ₀ Empty.rec* levelStoryΔ₀

  levelΣ₁ : Σ₁ σᴹ
  levelΣ₁ = mapΣ₁ Empty.rec* levelStoryΣ₁

  -- The two readings agree on the transported story: the delivered
  -- absoluteness at the restriction M, transitivity spent exactly at the
  -- bounded quantifiers.
  level-abs₀ : (δ : Sᴹ ^ 2) → (δ AbsM.⊨ᵐ σᴹ) ≡ ((map fst δ) AbsM.⊨ᵛ σᴹ)
  level-abs₀ δ = AbsM.abs₀ levelΔ₀ δ

  -- The crossing's transfer for the set-carrier level story: the inner
  -- reading implies the ambient reading (σ₁-up at M).
  level-transfer : TransferM σᴹ
  level-transfer v b = AbsM.σ₁-up levelΣ₁ (v ∷ b ∷ [])
```

<!--en-->
## The level story at the class carrier
<!--zh-->
## 类载体处的层故事
<!--/-->

<!--en-->
The mirror of the set-carrier story lives at the class carrier: the same
parameter-free axis, embedded at `Sʟ` instead of `Sᴹ`. The relabelling carries
the Delta-0 witness and the Sigma-1 witness exactly as before, and the Pi-1
instance of the tower transport is restated here, because the Pi-1 data
family, like the Sigma-1 family, has no delivered transport lemma and the
one-constructor instance is three lines at the Delta-0 leaf. The two readings
then agree at `L` by the delivered `abs₀` at the restriction, and both
transfers hold for the story itself: `σ₁-up` at `L` reads the inner story
into the ambient one, and `π₁-down` at `L` reads it back. The second
direction is the mechanism the crossing's `TransferL` will spend once the
story and the delivered description are known to agree; the agreement itself
is the class-carrier equivalence, stated in the crossing section below and
left standing with the ambient obligations.
<!--zh-->
集合载体故事的镜像住在类载体处：同一条无参轴，只是嵌入到 `Sʟ` 而非 `Sᴹ`。重标如旧携带 Δ₀ 见证与 Σ₁ 见证，而 Π₁ 型的塔运输在此重写，原因与 Σ₁ 数据族相同：Π₁ 数据族没有已交付的运输引理，单构造子实例在 Δ₀ 叶处只有三行。两条读式随后在 `L` 处由限制处的已交付 `abs₀` 一致，而两条转移对故事本身皆成立：`L` 处的 `σ₁-up` 把内层故事读进环境读式，`π₁-down` 把它读回。第二个方向正是跨越的 `TransferL` 将在「故事与已交付描述已知一致」之后消费的机制；那条一致本身，即类载体等价，在下方跨越一节陈述并留待与环境义务一同解决。
<!--/-->

```agda
  -- The Pi-1 instance of the delivered tower transport: one clause per
  -- constructor, `mapΔ₀` at the Delta-0 leaf (the mirror of `mapΣ₁`).
  mapΠ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        → {n : ℕ} {φ : Formula K n} → Π₁ φ → Π₁ (mapFo f φ)
  mapΠ₁ f (π-Δ₀ d) = π-Δ₀ (mapΔ₀ f d)
  mapΠ₁ f (π-∀ p)  = π-∀ (mapΠ₁ f p)

  -- The class-carrier level story: the parameter-free story embedded at Sʟ.
  σL : Formula Sʟ 2
  σL = embed levelStory

  -- The three witnesses ride the same relabelling.
  levelΔ₀L : Δ₀ σL
  levelΔ₀L = mapΔ₀ Empty.rec* levelStoryΔ₀

  levelΣ₁L : Σ₁ σL
  levelΣ₁L = mapΣ₁ Empty.rec* levelStoryΣ₁

  levelΠ₁L : Π₁ σL
  levelΠ₁L = mapΠ₁ Empty.rec* (π-Δ₀ levelStoryΔ₀)

  -- The two readings agree at the class carrier: the delivered
  -- absoluteness at the restriction L, transitivity spent at the bounded
  -- quantifiers exactly as at M.
  level-abs₀L : (δ : Sʟ ^ 2) → (δ AbsL.⊨ᵐ σL) ≡ ((map fst δ) AbsL.⊨ᵛ σL)
  level-abs₀L δ = AbsL.abs₀ levelΔ₀L δ

  -- Both transfers hold for the class-carrier story: inner to ambient by
  -- σ₁-up at L, and ambient to inner by π₁-down at L, the shape the
  -- crossing's `TransferL` spends at the description.
  level-transfer-up : (v b : Sʟ)
                    → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ σL ⟩
                    → ⟨ (fst v ∷ fst b ∷ []) AbsL.⊨ᵛ σL ⟩
  level-transfer-up v b = AbsL.σ₁-up levelΣ₁L (v ∷ b ∷ [])

  level-transfer-down : (v b : Sʟ)
                      → ⟨ (fst v ∷ fst b ∷ []) AbsL.⊨ᵛ σL ⟩
                      → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ σL ⟩
  level-transfer-down v b = AbsL.π₁-down levelΠ₁L (v ∷ b ∷ [])
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
machine-checked: the crossing's formula, the delivered description, is neither
Δ₀, Σ₁, nor Π₁ in the delivered certification, since its quantifier profile
carries unbounded quantifiers of both kinds, so none of the three delivered
transfer theorems applies. The Levy form of the level story is delivered above
at both carriers; the crossing's application of it, the equivalence with the
delivered description and the two factors of the ambient form, is the
obligation stated and reduced here. The limit case is stated as the target
`Condenses` but not built: it needs the ordinal predicate at the set carrier,
which the ordinal chapter ships carrier-generic and Δ₀-certified, and the two
inclusions, `M ⊆ L` (delivered above) and the reverse from `level-in` plus one
extensionality, priced in the report and left standing.
<!--zh-->
`TransferM` 与 `AmbientOnly` 都未交付，而探针机检地量到了原因：跨越的公式，即已交付的描述，在已交付的证书体系中既非 Δ₀、亦非 Σ₁、亦非 Π₁，因为它的量词画像同时携带两种无界量词，于是三条已交付的转移定理没有一条适用。层故事的 Lévy 形态已在上文两个载体处交付；跨越对它的施用，即与已交付描述之间的等价连同环境形态的两个因子，是在此陈述并化归的义务。极限情形被陈述为目标 `Condenses` 而未建造：它需要集合载体处的序数谓词，序数章以载体为参数、带 Δ₀ 证书地交付了它，还需要两条包含，`M ⊆ L` (上文已交付) 与由 `level-in` 加一次外延性得出的反向，在报告中定价并留待后继。
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
factorization proved. The Levy content of the level formula is delivered
above: the set-carrier story `σᴹ` and its class-carrier mirror `σL`, each with
its Sigma-1 witness and both readings, `σL` additionally Pi-1-certified. What
remains is the crossing's application of it, the equivalence with the
delivered description, the two factors of the ambient form, plus the limit
case; the collapse half is separately probed green and the hull separately
priced. The crossing is the face's third consumer, and the orchestrator wires
this chapter into `Everything`.
<!--zh-->
本章交付凝聚跨越的测得核心：传递集载体处的层句、后继情形及其两条伴生事实、保义的迁移，以及化归为「关于一条公式、在两个载体处的一条绝对性义务」的跨越，分解得证。层公式的 Lévy 内容已在上文交付：集合载体处的层故事 `σᴹ` 与它的类载体镜像 `σL`，各自连同 Σ₁ 见证与两条读式，`σL` 另带 Π₁ 证书。所余是跨越对它的施用，即与已交付描述之间的等价、环境形态的两个因子，连同极限情形；坍缩半边另有探针测得绿灯，外壳另有定价。跨越是面孔的第三个消费方，编排者把本章接入 `Everything`。
<!--/-->
