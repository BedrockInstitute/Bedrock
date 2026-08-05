# The hereditarily finite carrier

<!--en-->
The first limit of the rud tower, `Sset ω`, is the hereditarily finite
carrier: every member is finite, every finite stage is a member, and the
ordinals of the carrier are exactly the numerals. This chapter records the
pieces the carve at `ω` consumes. First the ordinal content of HF: an
ordinal member of HF is a numeral, the hard half `ord∈HF→∈ω`, lifted into
the tree from the carried-sequence probe. Then the over-HF identification:
the carrier-internal powerset of a finite stage is its next stage,
`powRel (Lset ζ) (Lset (sucV ζ))`, every subset of a finite stage lying in
HF being definable over the stage by its tally's mask. Finally the
strengthened bound discharged at the first limit, `strong-discharge ω`,
with the hard half as its hypothesis. The chapter's statements are
first-limit instances; the general transfer remains the recorded ×3 term of
the campaign.
<!--zh-->
初步函数塔的第一个极限 `Sset ω` 就是遗传有穷载体：每个成员都有穷，每个有穷阶段都是成员，而载体的序数恰是数码。本章记录 `ω` 处刻划消费的几件：首先是 HF 的序数内容，HF 中的序数成员必为数码，即硬半边 `ord∈HF→∈ω`，自携带序列探针搬入树中；然后是 HF 上的认同，有穷阶段的载体内幂集即其下一阶段，`powRel (Lset ζ) (Lset (sucV ζ))`，落在 HF 里的有穷阶段子集经该阶段点名册的掩码在其上可定义；最后是第一个极限处的加锐界兑付，`strong-discharge ω`，以硬半边为假设。本章的陈述都是第一个极限处的实例；一般性转移仍是战役所记的 ×3 项。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.HF {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using ( #∈ω; numeral-ord; ω-ord )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; finSet; finSet-in )
open import L.Rud.Step {ℓ} lem A using ( Sset; Sset-trans )
open import L.Rud.Bridge {ℓ} lem A using ( Lset-zero; Sset-union-limit )
open import L.Rud.BaseBlock {ℓ} lem A using
  ( limω; ∅∈Ssetω; baseStage∈J; sTally; module Power )
open import L.Rud.LevelSigma {ℓ} lem A using ( module LevelAt )
open import L.Choice.Finite {ℓ} lem using
  ( Tally; module PowerStep; maskAt; mask-onto; select; select-in; select-out
  ; marks; marks-lookup; decideOf; decide-true; decide-sound; module Search )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt )
open import V.Coding {ℓ} using ( #-inj′ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Fin.Base as FinΣ
open import Cubical.Data.Fin.Properties using ( pigeonhole-special; Fin-fst-≡ )
open import Cubical.Data.FinData.Base using ( toℕ )
open import Cubical.Data.FinData.Properties
  using ( toℕ<n; fromℕ'; inj-toℕ; toFromId' )
open import Cubical.Data.Bool using ( Bool; true )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The ordinals of HF
<!--zh-->
## HF 的序数
<!--/-->

<!--en-->
An ordinal member of HF is a numeral. The chain is the one the carried-
sequence probe built and verified, now given a home: a member of a finite
S-level is a subset of a tallied level, so it is tallied (marks plus select,
LEM); no tally of `ω` exists, by the finite pigeonhole on the numerals; a
finite ordinal is therefore a numeral, by trichotomy against `ω` with the
other two cases refuted by that tally obstruction; and membership in
`Sset ω` is membership in a finite level, by the delivered union read. The
four links are `subsetTally`, `notTallyω`, `finiteOrd→numeral` and
`ord∈HF→∈ω`.
<!--zh-->
HF 中的序数成员必为数码。这条链就是携带序列探针所建并验证过的那条，如今有了住处：有穷 S 层的成员是已清点层的子集，故可清点 (标记加 select，用排中律)；`ω` 没有点名册，由数码上的有穷鸽笼原理；有穷序数于是必为数码，与 `ω` 三歧、其余两情形被该点名册障碍驳倒；而 `Sset ω` 的成员即某个有穷层的成员，由已交付的并读式。四环即 `subsetTally`、`notTallyω`、`finiteOrd→numeral` 与 `ord∈HF→∈ω`。
<!--/-->

```agda
-- The numeral for k, named (the `#` prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

-- Inclusion, stated at the small membership.
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

-- A subset of a tallied set is tallied (marks + select, LEM).
subsetTally : (u : S) → Tally u → (y : S) → y ⊆ u → Tally y
subsetTally u t y sub = record
  { size = sel .fst
  ; item = sel .snd
  ; inside = inside'
  ; onto = onto' }
  where
  open Tally t
  d : S → Bool
  d z = decideOf (z ∈ˢ y) (lem (z ∈ˢ y))
  v : Vec Bool size
  v = marks size item d
  sel : Σ[ k ∈ ℕ ] (Fin k → S)
  sel = select size item v
  inside' : (j : Fin (sel .fst)) → ⟨ sel .snd j ∈ˢ y ⟩
  inside' j = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym (out .snd .snd))
    (decide-sound (item (out .fst) ∈ˢ y) (lem (item (out .fst) ∈ˢ y))
      (sym (marks-lookup size item d (out .fst)) ∙ out .snd .fst))
    where
    out : Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (sel .snd j ≡ item i))
    out = select-out size item v j
  onto' : (x : S) → ⟨ x ∈ˢ y ⟩ → ∥ Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ x) ∥₁
  onto' x x∈y = PT.map atIndex (onto x (sub x x∈y))
    where
    atIndex : Σ[ i ∈ Fin size ] (item i ≡ x)
            → Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ x)
    atIndex (i , q) = ins .fst , (ins .snd ∙ q)
      where
      ins : Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ item i)
      ins = select-in size item v i
        (marks-lookup size item d i ∙ decide-true (item i ∈ˢ y)
          (lem (item i ∈ˢ y)) (subst (λ w → ⟨ w ∈ˢ y ⟩) (sym q) x∈y))

-- No tally of ω: size+1 distinct numerals among size entries (pigeonhole).
notTallyω : Tally ω → Empty.⊥
notTallyω t = i≢j i≡j
  where
  open Tally t
  Idx : Type (ℓ-suc ℓ)
  Idx = Lift {ℓ-zero} {ℓ-suc ℓ} (Fin size)
  _≺_ : Idx → Idx → Type (ℓ-suc ℓ)
  a ≺ b = Lift {ℓ-zero} {ℓ-suc ℓ} (toℕ (a .lower) < toℕ (b .lower))
  tri : (a b : Idx) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
  tri a b = go (toℕ (a .lower) ≟ toℕ (b .lower))
    where
    go : NatOrder.Trichotomy (toℕ (a .lower)) (toℕ (b .lower))
       → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    go (NatOrder.lt h) = lt (lift {ℓ-zero} {ℓ-suc ℓ} h)
    go (NatOrder.gt h) = gt (lift {ℓ-zero} {ℓ-suc ℓ} h)
    go (NatOrder.eq p) = eq (cong (λ x → lift {ℓ-zero} {ℓ-suc ℓ} x) (inj-toℕ p))
  irr : (a : Idx) → a ≺ a → Empty.⊥
  irr a (lift h) = ¬m<m h
  trans : (a b c : Idx) → a ≺ b → b ≺ c → a ≺ c
  trans a b c (lift h) (lift k) = lift {ℓ-zero} {ℓ-suc ℓ} (<-trans h k)
  module S = Search {A = Idx} _≺_ tri irr trans
  module O = S.Over size (λ i → lift i) (λ a → ∣ a .lower , refl ∣₁)
  eqΩ : {x y : S} → Ω
  eqΩ {x} {y} = (x ≡ y) , setIsSet x y
  pick : (k : ℕ) → Fin size
  pick k = lower (O.least (λ j → eqΩ {item (lower j)} {nk k})
    (PT.map (λ { (i , q) → lift i , q }) (onto (nk k) (#∈ω k))) .fst)
  pick-eq : (k : ℕ) → item (pick k) ≡ nk k
  pick-eq k = O.least (λ j → eqΩ {item (lower j)} {nk k})
    (PT.map (λ { (i , q) → lift i , q }) (onto (nk k) (#∈ω k))) .snd .fst
  conv : {n : ℕ} → Fin n → FinΣ.Fin n
  conv i = toℕ i , toℕ<n i
  conv⁻¹ : {n : ℕ} → FinΣ.Fin n → Fin n
  conv⁻¹ {n} k = fromℕ' n (k .fst) (k .snd)
  f : Fin (suc size) → Fin size
  f i = pick (toℕ i)
  f' : FinΣ.Fin (suc size) → FinΣ.Fin size
  f' k = conv (f (conv⁻¹ k))
  collide : Σ[ i ∈ FinΣ.Fin (suc size) ] Σ[ j ∈ FinΣ.Fin (suc size) ]
              ((i ≡ j) → Empty.⊥) × (f' i ≡ f' j)
  collide = pigeonhole-special f'
  iΣ jΣ : FinΣ.Fin (suc size)
  iΣ = collide .fst
  jΣ = collide .snd .fst
  i j : Fin (suc size)
  i = conv⁻¹ iΣ
  j = conv⁻¹ jΣ
  i≢j : (i ≡ j) → Empty.⊥
  i≢j p = collide .snd .snd .fst
    (Fin-fst-≡ (sym (toFromId' (suc size) (iΣ .fst) (iΣ .snd))
               ∙ cong toℕ p
               ∙ toFromId' (suc size) (jΣ .fst) (jΣ .snd)))
  f≡ : f' iΣ ≡ f' jΣ
  f≡ = collide .snd .snd .snd
  f≡' : f i ≡ f j
  f≡' = inj-toℕ (cong fst f≡)
  num≡ : nk (toℕ i) ≡ nk (toℕ j)
  num≡ = sym (pick-eq (toℕ i)) ∙ cong item f≡' ∙ pick-eq (toℕ j)
  nat≡ : toℕ i ≡ toℕ j
  nat≡ = #-inj′ num≡
  i≡j : i ≡ j
  i≡j = inj-toℕ nat≡

-- A finite ordinal is a numeral (trichotomy vs ω; the other cases refute).
finiteOrd→numeral : (x : S) → IsOrd x → Tally x → ⟨ x ∈ˢ ω ⟩
finiteOrd→numeral x ordx tx = go (ord-tri x ordx ω ω-ord)
  where
  open Tally tx
  go : ⟨ x ∈ˢ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ˢ x ⟩) → ⟨ x ∈ˢ ω ⟩
  go (inl h) = h
  go (inr (inl p)) = Empty.rec (notTallyω (subst Tally p tx))
  go (inr (inr h)) = Empty.rec (notTallyω (subsetTally x tx ω ω⊆x))
    where
    ω⊆x : ω ⊆ x
    ω⊆x w w∈ω = ordx .fst w∈ω h

-- Ordinal in HF is a numeral (transitive finite level, tallied, then above).
ord∈HF→∈ω : (x : S) → IsOrd x → ⟨ x ∈ˢ Sset ω ⟩ → ⟨ x ∈ˢ ω ⟩
ord∈HF→∈ω x ordx x∈S = PT.rec (snd (x ∈ˢ ω)) atLevel
  (Sset-union-limit ω limω x x∈S)
  where
  atLevel : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Sset (sucV δ) ⟩) → ⟨ x ∈ˢ ω ⟩
  atLevel (δ , δ∈ω , x∈level) = PT.rec (snd (x ∈ˢ ω)) atNumeral δ∈ω
    where
    atNumeral : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ δ) → ⟨ x ∈ˢ ω ⟩
    atNumeral (m , q) = finiteOrd→numeral x ordx xTallied
      where
      level : S
      level = Sset (sucV (nk (lower m)))
      x∈level' : ⟨ x ∈ˢ Sset (sucV (nk (lower m))) ⟩
      x∈level' = subst (λ w → ⟨ x ∈ˢ w ⟩) (cong Sset (cong sucV (sym q))) x∈level
      x⊆level : x ⊆ level
      x⊆level z z∈x = Sset-trans (sucV (nk (lower m))) {x = x} {y = z}
        z∈x x∈level'
      xTallied : Tally x
      xTallied = subsetTally (Sset (sucV (nk (lower m))))
        (sTally (suc (lower m))) x x⊆level
```

<!--en-->
## The finite stages in HF
<!--zh-->
## HF 中的有穷阶段
<!--/-->

<!--en-->
Every finite stage is a member of HF, by the base block's successor
membership iterated along the numeral. This is the tower hypothesis at `ω`,
and it is the certificate the over-HF identification needs for the next
stage's membership.
<!--zh-->
每个有穷阶段都是 HF 的成员，由基块的后继隶属沿数码迭代。这正是 `ω` 处的塔假设，也是 HF 上认同所需的「下一阶段在载体中」的证书。
<!--/-->

```agda
-- Every finite stage is an HF member: the tower hypothesis at ω.
stage∈HF : (ζ : S) → ⟨ ζ ∈ˢ ω ⟩ → ⟨ Lset ζ ∈ˢ Sset ω ⟩
stage∈HF ζ ζ∈ω = PT.rec (snd (Lset ζ ∈ˢ Sset ω)) go ζ∈ω
  where
  numeralStage : (k : ℕ) → ⟨ Lset (# k) ∈ˢ Sset ω ⟩
  numeralStage zero = subst (λ w → ⟨ w ∈ˢ Sset ω ⟩) (sym Lset-zero) ∅∈Ssetω
  numeralStage (suc k) = baseStage∈J (# k) (#∈ω k) (numeralStage k)
  go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ ζ) → ⟨ Lset ζ ∈ˢ Sset ω ⟩
  go (m , q) = subst (λ w → ⟨ Lset w ∈ˢ Sset ω ⟩) q (numeralStage (lower m))
```

<!--en-->
## The over-HF identification
<!--zh-->
## HF 上的认同
<!--/-->

<!--en-->
The strengthened story's successor clause is written against the carrier-
internal powerset relation `powRel` of the level-sigma chapter, instantiated
here at the hereditarily finite carrier `Sset ω`. Over HF the internal
powerset of a finite stage is its next stage: the next stage is a member of
HF, every member of the next stage is a subset of the stage, and every
subset of the stage lying in HF is a member of the next stage. The third
inclusion is the mask round trip: a subset of a finite stage is a part of
its tally's mask, every part is a member of the stage's definable power, and
the definable power is the next stage. The relation is functional, so the
identification reads as an equality of the powerset's unique value.
<!--zh-->
加锐故事的后继值子句对照层 sigma 章的载体内幂集关系 `powRel` 写出，此处实例化于遗传有穷载体 `Sset ω`。在 HF 上，有穷阶段的载体内幂集即其下一阶段：下一阶段是 HF 的成员，下一阶段的每个成员都是该阶段的子集，而落在 HF 里的该阶段每个子集都是下一阶段的成员。第三条包含即掩码来回：有穷阶段的子集是其点名册某掩码的 part，每个 part 都是该阶段可定义幂的成员，而可定义幂就是下一阶段。该关系是函数的，故认同读作幂集唯一值的等式。
<!--/-->

```agda
-- The carrier-internal powerset at the first limit, instantiated at HF.
module LA = LevelAt ω limω (∈-asFiber {a = ∅} {b = Sset ω} ∅∈Ssetω .fst)

-- The mask round trip with a subset hypothesis: every subset of a finite
-- stage is a part of its tally's mask.
subset-part-mask : (σ : S) (oσ : IsOrd σ) (t : Tally (Lset σ)) (x : S)
                 → x ⊆ Lset σ → PowerStep.part σ oσ t (PowerStep.maskOf σ oσ t x) ≡ x
subset-part-mask σ oσ t x x⊆ = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
  where
  module PS = PowerStep σ oσ t
  open Tally t
  fwd : (y : S) → ⟨ y ∈ˢ PS.part (PS.maskOf x) ⟩ → ⟨ y ∈ˢ x ⟩
  fwd y y∈ = PT.rec (snd (y ∈ˢ x)) step (PS.part-out (PS.maskOf x) y y∈)
    where
    step : Σ[ i ∈ Fin size ] ((lookup i (PS.maskOf x) ≡ true) × (item i ≡ y))
         → ⟨ y ∈ˢ x ⟩
    step (i , e , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) q
      (decide-sound (item i ∈ˢ x) (lem (item i ∈ˢ x))
        (sym (marks-lookup size item (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i) ∙ e))
  bwd : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ PS.part (PS.maskOf x) ⟩
  bwd y y∈x = PT.rec (snd (y ∈ˢ PS.part (PS.maskOf x))) step (onto y (x⊆ y y∈x))
    where
    step : Σ[ i ∈ Fin size ] (item i ≡ y) → ⟨ y ∈ˢ PS.part (PS.maskOf x) ⟩
    step (i , q) = subst (λ w → ⟨ w ∈ˢ PS.part (PS.maskOf x) ⟩) q
      (PS.part-mem (PS.maskOf x) i
        (marks-lookup size item (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i
         ∙ decide-true (item i ∈ˢ x) (lem (item i ∈ˢ x))
             (subst (λ w → ⟨ w ∈ˢ x ⟩) (sym q) y∈x)))

-- The over-HF identification at the numerals: the internal powerset of a
-- finite stage is the next stage.
powRel-Lset# : (k : ℕ) → LA.powRel (Lset (# k)) (Lset (# (suc k)))
powRel-Lset# k = ( next∈ , ( memb , closed ) )
  where
  σ : S
  σ = # k
  L∈ : ⟨ Lset σ ∈ˢ Sset ω ⟩
  L∈ = stage∈HF σ (#∈ω k)
  module P = Power k L∈
  next∈ : ⟨ Lset (sucV σ) ∈ˢ Sset ω ⟩
  next∈ = baseStage∈J σ (#∈ω k) L∈
  memb : (z : S) → ⟨ z ∈ˢ Lset (sucV σ) ⟩ → z ⊆ Lset σ
  memb z z∈ w w∈z = 𝒟ₒ∋⊆ (Lset σ) z z∈𝒟 w w∈z
    where
    z∈𝒟 : ⟨ z ∈ˢ 𝒟ₒ (Lset σ) ⟩
    z∈𝒟 = subst (λ u → ⟨ z ∈ˢ u ⟩) (Lset-suc σ) z∈
  closed : (z : S) → ⟨ z ∈ˢ Sset ω ⟩ → z ⊆ Lset σ → ⟨ z ∈ˢ Lset (sucV σ) ⟩
  closed z z∈u z⊆ = subst (λ u → ⟨ z ∈ˢ u ⟩) (sym (Lset-suc σ)) z∈𝒟
    where
    z∈fin : ⟨ z ∈ˢ finSet P.M P.fam ⟩
    z∈fin = finSet-in P.M P.fam z ∣ j
      , (cong P.PS.part (mo .snd)
         ∙ subset-part-mask σ (numeral-ord k) P.t z z⊆) ∣₁
      where
      mo : Σ[ j ∈ Fin P.M ] (maskAt (Tally.size P.t) j ≡ P.PS.maskOf z)
      mo = mask-onto (Tally.size P.t) (P.PS.maskOf z)
      j : Fin P.M
      j = mo .fst
    z∈𝒟 : ⟨ z ∈ˢ 𝒟ₒ (Lset σ) ⟩
    z∈𝒟 = subst (λ u → ⟨ z ∈ˢ u ⟩) (sym (P.defPow≡finSet)) z∈fin

isPropPowRel : (ζ : S) → isProp (LA.powRel (Lset ζ) (Lset (sucV ζ)))
isPropPowRel ζ = isProp× (snd (Lset (sucV ζ) ∈ˢ Sset ω))
  (isProp× (isPropΠ2 (λ z _ → isPropΠ2 (λ w _ → snd (w ∈ˢ Lset ζ))))
           (isPropΠ3 (λ z _ _ → snd (z ∈ˢ Lset (sucV ζ)))))

-- The over-HF identification, at any finite stage.
powRel-Lset-suc : (ζ : S) → ⟨ ζ ∈ˢ ω ⟩ → LA.powRel (Lset ζ) (Lset (sucV ζ))
powRel-Lset-suc ζ ζ∈ω = PT.rec (isPropPowRel ζ) go ζ∈ω
  where
  go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ ζ) → LA.powRel (Lset ζ) (Lset (sucV ζ))
  go (m , q) = subst (λ w → LA.powRel (Lset w) (Lset (sucV w))) q
    (powRel-Lset# (lower m))

-- The internal powerset is functional, by extensionality of the two
-- inclusions.
powRel-unique : (c b₁ b₂ : S) → LA.powRel c b₁ → LA.powRel c b₂ → b₁ ≡ b₂
powRel-unique c b₁ b₂ (b₁∈u , memb₁ , closed₁) (b₂∈u , memb₂ , closed₂) =
  extensionalV (λ z → ⇔toPath (to₂ z) (to₁ z))
  where
  to₂ : (z : S) → ⟨ z ∈ˢ b₁ ⟩ → ⟨ z ∈ˢ b₂ ⟩
  to₂ z z∈b₁ = closed₂ z (LA.utr {x = b₁} {y = z} z∈b₁ b₁∈u) (memb₁ z z∈b₁)
  to₁ : (z : S) → ⟨ z ∈ˢ b₂ ⟩ → ⟨ z ∈ˢ b₁ ⟩
  to₁ z z∈b₂ = closed₁ z (LA.utr {x = b₂} {y = z} z∈b₂ b₂∈u) (memb₂ z z∈b₂)

-- The internal powerset of a finite stage is exactly the next stage.
powRel-Lset-suc-unique : (ζ : S) → ⟨ ζ ∈ˢ ω ⟩ → (b : S)
                       → LA.powRel (Lset ζ) b → b ≡ Lset (sucV ζ)
powRel-Lset-suc-unique ζ ζ∈ω b pb =
  powRel-unique (Lset ζ) b (Lset (sucV ζ)) pb (powRel-Lset-suc ζ ζ∈ω)
```

<!--en-->
## The strengthened bound at the first limit
<!--zh-->
## 第一个极限处的加锐界
<!--/-->

<!--en-->
The strengthened domain bound discharges wherever every ordinal of the
carrier lies in the bound. At the first limit the carrier is HF, the bound
is `ω`, and the hypothesis is exactly the hard half `ord∈HF→∈ω`: every
ordinal member of HF is a numeral. The instantiation is one call to the
delivered discharge.
<!--zh-->
加锐定义域界在「载体的每个序数都落在界里」之处兑付。第一个极限处载体是 HF、界是 `ω`，而假设恰是硬半边 `ord∈HF→∈ω`：HF 的每个序数成员都是数码。该实例化是对已交付兑付的一次调用。
<!--/-->

```agda
-- The strengthened bound at the first limit: dom f ⊆ ω from ordDom f.
strong-discharge-ω : (f : S) → LA.ordDom f → LA.strongDomOrd ω f
strong-discharge-ω f ord = LA.strong-discharge ω f
  (λ a oa a∈u → ord∈HF→∈ω a oa a∈u) ord
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The hereditarily finite carrier now carries the carve's first-limit
ingredients: the ordinal content of HF (`ord∈HF→∈ω`, the hard half, with
its three-link chain), the over-HF identification (`powRel-Lset-suc` with
`powRel-Lset-suc-unique`), and the strengthened bound discharged at `ω`
(`strong-discharge-ω`). What this chapter does not build is the family
equality itself: the delivered successor-value clause is two-way, and over
HF, with the identification in hand, it forces an infinite chain, so the
recorded five-clause story has no finite witness; the carve needs the
classical one-way successor clause with the exact domain bound, reported
and priced beside the delivered seam.
<!--zh-->
遗传有穷载体如今载有刻划在第一个极限处的成分：HF 的序数内容 (`ord∈HF→∈ω`，即硬半边，连同其三条链)、HF 上的认同 (`powRel-Lset-suc` 与 `powRel-Lset-suc-unique`)、以及在 `ω` 处兑付的加锐界 (`strong-discharge-ω`)。本章不建族等式本身：已交付的后继值子句是双向的，而在 HF 上、认同在手，它逼出无穷链，故所记五合取故事没有有穷见证；刻划需要经典的单向后继子句连同精确定义域界，报告在已交付接缝旁记下并定价。
<!--/-->
