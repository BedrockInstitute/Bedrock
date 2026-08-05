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
open import FOL.Syntax using ( Formula; ∃̇_; _∧̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-out; Lset-mono; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using
  ( ∅-ord; ∈#-elim; #∈ω; numeral-mem; numeral-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.InitialSegment {ℓ} using ( _∈ran_; _⟷_ )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; finSet; finSet-in; finSet-out )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-trans; limit-succ-mem; Jset-rud; f5; f9; Fof-f5; Fof-f9 )
open import L.Rud.Bridge {ℓ} lem A using
  ( Lset-zero; Sset-union-limit; γ; γ-compute; γ-suc; γ-lim; γ-mono; U-zero
  ; Lset-union-limit )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-in; +ω-out; +ω-mem; sucIter )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import L.Rud.LevelSigma {ℓ} lem A using ( module LevelAt )
open import L.Rud.Finite {ℓ} lem A using
  ( limω; ∅∈Ssetω; baseStage∈J; op-in-J; finSetMem; sTally; module Power; ltally
  ; Tally; module PowerStep; maskAt; mask-onto; select; select-in; select-out
  ; marks; marks-lookup; decideOf; decide-true; decide-sound; module Search )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( _<_; ≤-refl; <-trans; ¬m<m; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Fin.Base as FinΣ
open import Cubical.Data.Fin.Properties using ( pigeonhole-special; Fin-fst-≡ )
open import Cubical.Data.FinData.Base using ( toℕ; zero )
open import Cubical.Data.FinData.Properties
  using ( toℕ<n; fromℕ'; inj-toℕ; toFromId' )
open import Cubical.Data.Bool using ( Bool; true )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ∈∈ₛ; _∈ₛ_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; module InfinitySet )
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
  module P = Power k L∈ (ltally k)
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

<!--en-->
## The one-way carve at the first limit
<!--zh-->
## 第一个极限处的单侧刻划
<!--/-->

<!--en-->
The classical story at the carrier is the one-way successor-value clause with
the exact domain bound, delivered in the level-sigma chapter and instantiated
here. Two consequences close the carve's non-overshoot side. First the value
chain: a witness of the one-way story is honest, a present pair's value at an
index in `ω` is the L-stage at that index, by induction on the numeral, with
the exact domain supplying the chain's totality, transitivity the descent, and
the over-HF identification the step. Second the family formula: `ψ` exists a
carrier member satisfying the one-way story and ranging over `x`, and its
satisfaction decodes to the meta story through the delivered reassembly.
Then every member of the carve `defSet (Sset ω) ψ` is an L-stage below `ω`:
the range membership puts its first component in the exact domain, the
ordinal content of HF moves the bound into `ω`, transitivity moves the
component with it, and the value chain identifies the value.
<!--zh-->
载体处的经典故事是带精确定义域界的单向后继值子句，由层 sigma 章交付、此处实例化。两个推论关闭刻划的「不越界」侧。先是值链：单向故事的见证是诚实的，`ω` 中索引处已现之对的值就是该索引处的 L 阶段，沿数码归纳，精确界供给链的完全性、传递性供给下行、HF 上的认同供给步。再是族公式：`ψ` 存在一个满足单向故事且以 `x` 为像的载体成员，其满足经已交付的重新装配解码到元层故事。于是刻划 `defSet (Sset ω) ψ` 的每个成员都是 `ω` 之下的 L 阶段：像的隶属把首分量放进精确界，HF 的序数内容把界移进 `ω`，传递性把分量一并带入，值链再把值认同。
<!--/-->

```agda
-- The internal-powerset relation is a proposition at any pair.
powRelProp : (c b : S) → isProp (LA.powRel c b)
powRelProp c b = isProp× (snd (b ∈ˢ Sset ω))
  (isProp× (isPropΠ2 (λ z _ → isPropΠ2 (λ w _ → snd (w ∈ˢ c))))
           (isPropΠ3 (λ z _ _ → snd (z ∈ˢ b))))

-- The value chain: a present pair's value at an index in ω is the L-stage.
chainValue : (f : S) → LA.aSt1 f → (a x : S) → ⟨ a ∈ˢ ω ⟩
           → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Lset a
chainValue f st a x a∈ω ax∈f = PT.rec (setIsSet x (Lset a)) go a∈ω
  where
  h4 : LA.exactDom f
  h4 = st .snd .snd .snd .fst
  chainNum : (n : ℕ) (x : S) → ⟨ pr (# n) x ∈ˢ f ⟩ → x ≡ Lset (# n)
  chainNum zero x px = x≡∅ ∙ sym Lset-zero
    where
    x≡∅ : x ≡ ∅
    x≡∅ = PT.rec (setIsSet x ∅) zStep (st .snd .snd .fst)
      where
      zStep : Σ[ a ∈ S ]
               ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ f ⟩ ) → x ≡ ∅
      zStep (a , (emp , aa∈f)) = st .snd .fst ∅ x ∅ px pr∅∅
        where
        a≡∅ : a ≡ ∅
        a≡∅ = extensionalV (λ z → ⇔toPath
          (λ z∈a → Empty.rec (emp z z∈a))
          (λ z∈∅ → Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))))
        pr∅∅ : ⟨ pr ∅ ∅ ∈ˢ f ⟩
        pr∅∅ = subst (λ w → ⟨ pr w w ∈ˢ f ⟩) a≡∅ aa∈f
  chainNum (suc n) x px = PT.rec (setIsSet x (Lset (# (suc n)))) δStep h4
    where
    δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Sset ω ⟩ × IsOrd δ
             × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
             × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
          → x ≡ Lset (# (suc n))
    δStep (δ , (δ∈u , ordδ , in-dir , out-dir)) =
      powRel-Lset-suc-unique (# n) (#∈ω n) x pb
      where
      suc∈δ : ⟨ sucV (# n) ∈ˢ δ ⟩
      suc∈δ = out-dir (sucV (# n)) ∣ x , px ∣₁
      n∈δ : ⟨ nk n ∈ˢ δ ⟩
      n∈δ = ordδ .fst {x = sucV (# n)} {y = # n} (self∈sucV (# n)) suc∈δ
      pb : LA.powRel (Lset (# n)) x
      pb = PT.rec (powRelProp (Lset (# n)) x) cStep (in-dir (# n) n∈δ)
        where
        cStep : Σ[ c ∈ S ] ⟨ pr (# n) c ∈ˢ f ⟩ → LA.powRel (Lset (# n)) x
        cStep (c , prnc) = st .snd .snd .snd .snd (# n) (Lset (# n)) x prn px
          where
          prn : ⟨ pr (# n) (Lset (# n)) ∈ˢ f ⟩
          prn = subst (λ w → ⟨ pr (# n) w ∈ˢ f ⟩) (chainNum n c prnc) prnc
  go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ a) → x ≡ Lset a
  go (m , q) = subst (λ w → x ≡ Lset w) q (chainNum (lower m) x ax∈f')
    where
    ax∈f' : ⟨ pr (# (lower m)) x ∈ˢ f ⟩
    ax∈f' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym q) ax∈f

-- The family formula: a carrier member satisfies the one-way story and
-- ranges over x.
ψ : Formula ⟪ Sset ω ⟫ 1
ψ = ∃̇ (LA.aStForm1 ∧̇ LA.Rg)

-- Satisfaction of ψ decodes to the meta story, with the range read.
ψ-out : (x : ⟪ Sset ω ⟫) → ⟨ (LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ ⟩
      → ∥ Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f)) ∥₁
ψ-out x = PT.map go
  where
  go : Σ[ f ∈ LA.U.SM ] ⟨ (f ∷ LA.U.ι x ∷ []) LA.U.⊨ᵐ (LA.aStForm1 ∧̇ LA.Rg) ⟩
     → Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f))
  go (f , (st , rg)) = f , (LA.aSt1-ok f x .fst st , LA.r-ok f x .fst rg)

-- The carve does not overshoot: every carved member is an L-stage below ω.
carve-⊇ : (y : S) → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
        → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
carve-⊇ y y∈ = fStep
  (∈-asFiber {a = y} {b = Sset ω} (LA.U.defSet⊆A ψ y y∈))
  where
  fStep : Σ[ m ∈ ⟪ Sset ω ⟫ ] (⟪ Sset ω ⟫↪ m ≡ y)
        → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
  fStep (m , q) = PT.rec squash₁ wStep (ψ-out m sat)
    where
    sat : ⟨ (LA.U.ι m ∷ []) LA.U.⊨ᵐ ψ ⟩
    sat = subst ⟨_⟩ (LA.U.defSet-mem ψ m)
      (subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (sym q) y∈)
    wStep : Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ m ∈ran fst f))
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
    wStep (f , (st , r)) = PT.rec squash₁ aStep r
      where
      aStep : Σ[ a ∈ S ] ⟨ pr a (⟪ Sset ω ⟫↪ m) ∈ˢ fst f ⟩
            → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
      aStep (a , pr∈) = PT.rec squash₁ dStep (st .snd .snd .snd .fst)
        where
        dStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Sset ω ⟩ × IsOrd δ
                 × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁)
                 × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
              → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
        dStep (δ , (δ∈u , ordδ , _ , out-d)) = ∣ a , (a∈ω , y≡Lseta) ∣₁
          where
          a∈δ : ⟨ a ∈ˢ δ ⟩
          a∈δ = out-d a ∣ ⟪ Sset ω ⟫↪ m , pr∈ ∣₁
          δ∈ω : ⟨ δ ∈ˢ ω ⟩
          δ∈ω = ord∈HF→∈ω δ ordδ δ∈u
          a∈ω : ⟨ a ∈ˢ ω ⟩
          a∈ω = ω-ord .fst {x = δ} {y = a} a∈δ δ∈ω
          y≡Lseta : y ≡ Lset a
          y≡Lseta = sym q ∙ chainValue (fst f) st a (⟪ Sset ω ⟫↪ m) a∈ω pr∈
```

<!--en-->
## The tower arithmetic at the first limit

The full switch lands the family one ω-block above the running sup, at the
pair `(γ ω, ω)`, and its certificate `β ∈ α` is the membership of the first
limit in its own tower value. The membership is the first-limit arithmetic
the carried-sequence probe built: the first ω-block above zero is the first
limit (`+ω ∅ = ω`), the tower at zero is that limit (`γ ∅ = ω`), the
successor value at zero holds it (`ω ∈ γ 1`), and the tower's monotonicity
carries it to `ω ∈ γ ω`. The four links are recorded here, discharged from
delivered tower machinery.
<!--zh-->
## 第一个极限处的塔算术

完全切换把族送到运行上确界之上一个 ω 块处，即那一对 `(γ ω, ω)`，其证书 `β ∈ α` 就是第一个极限在自身塔值中的隶属。该隶属就是携带序列探针所建的第一个极限算术：零之上的第一个 ω 块就是第一个极限 (`+ω ∅ = ω`)，塔在零处的值就是那个极限 (`γ ∅ = ω`)，零处的后继值持有它 (`ω ∈ γ 1`)，塔的单调性再把它带到 `ω ∈ γ ω`。四环都记在此，由已交付的塔机器兑付。
<!--/-->

```agda
-- Extensional equality from the two inclusions (the small membership).
ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- The iterated successors of zero are exactly the numerals.
sucIter∅≡# : (n : ℕ) → sucIter n ∅ ≡ # n
sucIter∅≡# zero = refl
sucIter∅≡# (suc n) = cong sucV (sucIter∅≡# n)

-- The first ω-block above zero is the first limit: +ω ∅ ≡ ω.
+ω∅≡ω : +ω ∅ ≡ ω
+ω∅≡ω = ext-⊆ sub sup
  where
  sub : +ω ∅ ⊆ ω
  sub x x∈ = PT.rec (snd (x ∈ˢ ω)) go (+ω-out ∅ x x∈)
    where
    go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) ∅ ⟩ → ⟨ x ∈ˢ ω ⟩
    go (n , x∈) = numeral-mem (suc n) x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (sucIter∅≡# (suc n)) x∈)
  sup : ω ⊆ +ω ∅
  sup x x∈ = PT.rec (snd (x ∈ˢ +ω ∅)) go x∈
    where
    go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ x) → ⟨ x ∈ˢ +ω ∅ ⟩
    go (m , q) = subst (λ w → ⟨ w ∈ˢ +ω ∅ ⟩) q
      (+ω-in ∅ nm (lower m) h)
      where
      nm : S
      nm = # (lower m)
      h : ⟨ nm ∈ˢ sucIter (suc (lower m)) ∅ ⟩
      h = subst (λ w → ⟨ nm ∈ˢ w ⟩)
            (sym (sucIter∅≡# (suc (lower m))))
            (self∈sucV nm)

-- The tower at zero is the first limit: γ ∅ = +ω (U ∅) = +ω ∅ = ω.
γ∅≡ω : γ ∅ ≡ ω
γ∅≡ω = subst (λ w → γ ∅ ≡ +ω w) U-zero (γ-compute ∅) ∙ +ω∅≡ω

-- ω ∈ γ 1 = +ω (γ ∅).
ω∈γ1 : ⟨ ω ∈ˢ γ (sucV ∅) ⟩
ω∈γ1 = subst (λ w → ⟨ w ∈ˢ γ (sucV ∅) ⟩) γ∅≡ω
  (subst (λ w → ⟨ γ ∅ ∈ˢ w ⟩) (sym (γ-suc ∅ ∅-ord)) (+ω-mem (γ ∅)))

-- The first limit lies in its own tower value, by the tower's monotonicity.
ω∈γω : ⟨ ω ∈ˢ γ ω ⟩
ω∈γω = γ-mono ω (sucV ∅) ω-ord (#∈ω 1) ω ω∈γ1
```

<!--en-->
## The honest segments and the family equality

The carve's missing direction, that every L-stage below `ω` is carved, is
served by the honest segment of length `n`, the finite table of the pairs
`(k, Lset k)` for `k ≤ n`. The segment is a carrier member by the finite
table lemma, and the five clauses of the one-way story are checked on it:
pairhood and single-valuedness by the pair injections, the zero clause by
the base stage, the exact domain by the numeral's members being exactly the
smaller numerals, and the one-way successor clause by the over-HF
identification at the index's numeral. The satisfaction of the family
formula is then assembled from the meta story, and the two directions of
the family equality close membership-wise.
<!--zh-->
## 诚实段与族等式

刻划所缺的方向，即 `ω` 之下的每个 L 阶段都被刻入，由长度 `n` 的诚实段服务，也就是 `k ≤ n` 诸对 `(k, Lset k)` 所成的有穷表。段经有穷表引理成为载体成员，单向故事的五条子句都在其上核对：成对性与单值性经对注入，零子句经基阶段，精确界经「数码的成员恰是更小的数码」，单向后继子句经索引数码处的 HF 上认同。族公式的满足随之从元层故事装配出来，族等式的两个方向按成员关系闭合。
<!--/-->

```agda
-- Numerals are members of Lset ω (the ordinal content of the first stage).
numeral∈Lsetω : (k : ℕ) → ⟨ nk k ∈ˢ Lset ω ⟩
numeral∈Lsetω k = Lset-mono {α = ω} {β = sucV (nk k)} (#∈ω (suc k))
  (ord∈Lset-suc (nk k) (numeral-ord k))

-- The first L-stage is a subset of HF, through the tower hypothesis at ω.
Lsetω⊆Ssetω : Lset ω ⊆ Sset ω
Lsetω⊆Ssetω x x∈L = PT.rec (snd (x ∈ˢ Sset ω)) go (Lset-out ω x x∈L)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ˢ Sset ω ⟩
  go (δ , δ∈ω , x∈𝒟) = Sset-trans ω
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟)
    (baseStage∈J δ δ∈ω (stage∈HF δ δ∈ω))

-- Numerals are HF members.
numeral∈HF : (k : ℕ) → ⟨ nk k ∈ˢ Sset ω ⟩
numeral∈HF k = Lsetω⊆Ssetω (nk k) (numeral∈Lsetω k)

-- Pairing closes in HF.
pr-in-HF : (a b : S) → ⟨ a ∈ˢ Sset ω ⟩ → ⟨ b ∈ˢ Sset ω ⟩ → ⟨ pr a b ∈ˢ Sset ω ⟩
pr-in-HF a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset ω ⟩) (Fof-f9 a b) (op-in-J f9 a b a∈ b∈)

-- The honest segment of length n: the pairs (k, Lset k) for k ≤ n.
seg : (n : ℕ) → S
seg n = finSet (suc n) (λ i → pr (nk (toℕ i)) (Lset (nk (toℕ i))))

seg∈HF : (n : ℕ) → ⟨ seg n ∈ˢ Sset ω ⟩
seg∈HF n = finSetMem (suc n) h (λ i → pr-in-HF (nk (toℕ i)) (Lset (nk (toℕ i)))
  (numeral∈HF (toℕ i)) (stage∈HF (nk (toℕ i)) (#∈ω (toℕ i))))
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))

-- Pairhood: every segment member is a Kuratowski pair.
segPair : (n : ℕ) (z : S) → ⟨ z ∈ˢ seg n ⟩ → isPair z
segPair n z z∈ = PT.rec squash₁ go (finSet-out (suc n) h z z∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go : Σ[ i ∈ Fin (suc n) ] (pr (nk (toℕ i)) (Lset (nk (toℕ i))) ≡ z) → isPair z
  go (i , q) = ∣ nk (toℕ i) , (Lset (nk (toℕ i)) , sym q) ∣₁

-- Single-valuedness: equal first components force equal values.
segSingle : (n : ℕ) → LA.singleValued (seg n)
segSingle n a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁
  (finSet-out (suc n) h (pr a b) ab∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → b ≡ c
  go₁ (i , q₁) = PT.rec (setIsSet b c) go₂
    (finSet-out (suc n) h (pr a c) ac∈)
    where
    a≡#i : a ≡ nk (toℕ i)
    a≡#i = pr-inj (sym q₁) .fst
    b≡ : b ≡ Lset (nk (toℕ i))
    b≡ = pr-inj (sym q₁) .snd
    go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr a c) → b ≡ c
    go₂ (j , q₂) = b≡ ∙ cong Lset (cong nk (#-inj′ {toℕ i} {toℕ j} #i≡#j))
                 ∙ sym (pr-inj (sym q₂) .snd)
      where
      #i≡#j : nk (toℕ i) ≡ nk (toℕ j)
      #i≡#j = sym a≡#i ∙ pr-inj (sym q₂) .fst

-- The zero clause: the segment maps the empty set to itself.
segZero : (n : ℕ) → LA.zeroClause (seg n)
segZero n = ∣ ∅ , (empt , pair) ∣₁
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  idx : Fin (suc n)
  idx = zero
  h-idx : h idx ≡ pr ∅ ∅
  h-idx = cong₂ pr refl Lset-zero
  empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
  empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
  pair : ⟨ pr ∅ ∅ ∈ˢ seg n ⟩
  pair = finSet-in (suc n) h (pr ∅ ∅) ∣ idx , h-idx ∣₁

-- The exact domain of the segment: the ordinal # (suc n).
segDom : (n : ℕ) → LA.exactDom (seg n)
segDom n = ∣ nk (suc n) , ( numeral∈HF (suc n) , numeral-ord (suc n)
  , in-dir , out-dir ) ∣₁
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  in-dir : (a : S) → ⟨ a ∈ˢ nk (suc n) ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
  in-dir a a∈ = PT.rec squash₁ go (∈#-elim (suc n) a a∈)
    where
    go : Σ[ m ∈ ℕ ] ((m < suc n) × (a ≡ nk m)) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
    go (m , (p , q)) = ∣ Lset (nk m) , pair∈ ∣₁
      where
      idx : Fin (suc n)
      idx = fromℕ' (suc n) m p
      e : toℕ idx ≡ m
      e = toFromId' (suc n) m p
      h-idx : h idx ≡ pr (nk m) (Lset (nk m))
      h-idx = cong₂ pr (cong nk e) (cong Lset (cong nk e))
      pair∈ : ⟨ pr a (Lset (nk m)) ∈ˢ seg n ⟩
      pair∈ = finSet-in (suc n) h (pr a (Lset (nk m)))
        ∣ idx , (h-idx ∙ cong₂ pr (sym q) refl) ∣₁
  out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁ → ⟨ a ∈ˢ nk (suc n) ⟩
  out-dir a = PT.rec (snd (a ∈ˢ nk (suc n))) go
    where
    go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ → ⟨ a ∈ˢ nk (suc n) ⟩
    go (b , ab∈) = PT.rec (snd (a ∈ˢ nk (suc n))) go₂
      (finSet-out (suc n) h (pr a b) ab∈)
      where
      go₂ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → ⟨ a ∈ˢ nk (suc n) ⟩
      go₂ (i , q) = subst (λ w → ⟨ w ∈ˢ nk (suc n) ⟩)
        (sym (pr-inj (sym q) .fst)) (#mono (toℕ i) (suc n) (toℕ<n i))

-- The one-way successor clause holds on the segment.
segSucc1 : (n : ℕ) → LA.succValClause1 (seg n)
segSucc1 n a c b ac∈ ab∈ = PT.rec (powRelProp c b) go₁
  (finSet-out (suc n) h (pr a c) ac∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a c) → LA.powRel c b
  go₁ (i , q₁) = PT.rec (powRelProp c b) go₂
    (finSet-out (suc n) h (pr (sucV a) b) ab∈)
    where
    a≡#i : a ≡ nk (toℕ i)
    a≡#i = pr-inj (sym q₁) .fst
    c≡Lseta : c ≡ Lset a
    c≡Lseta = pr-inj (sym q₁) .snd ∙ cong Lset (sym a≡#i)
    a∈ω : ⟨ a ∈ˢ ω ⟩
    a∈ω = subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym a≡#i) (#∈ω (toℕ i))
    go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr (sucV a) b) → LA.powRel c b
    go₂ (j , q₂) = subst (λ w → LA.powRel c w) (sym b≡)
      (subst (λ w → LA.powRel w (Lset (sucV a))) (sym c≡Lseta)
        (powRel-Lset-suc a a∈ω))
      where
      sucV-a≡#i' : sucV a ≡ nk (suc (toℕ i))
      sucV-a≡#i' = cong sucV a≡#i
      #i'≡#j : nk (suc (toℕ i)) ≡ nk (toℕ j)
      #i'≡#j = sym sucV-a≡#i' ∙ pr-inj (sym q₂) .fst
      b≡ : b ≡ Lset (sucV a)
      b≡ = pr-inj (sym q₂) .snd
         ∙ sym (cong Lset (cong nk (#-inj′ {suc (toℕ i)} {toℕ j} #i'≡#j)))
         ∙ cong Lset (cong sucV (sym a≡#i))

-- The value Lset (# m) lies in the range of its own segment.
segRan : (m : ℕ) → Lset (nk m) ∈ran seg m
segRan m = ∣ nk m , pair ∣₁
  where
  h : Fin (suc m) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  idx : Fin (suc m)
  idx = fromℕ' (suc m) m (≤-refl {suc m})
  e : toℕ idx ≡ m
  e = toFromId' (suc m) m (≤-refl {suc m})
  h-idx : h idx ≡ pr (nk m) (Lset (nk m))
  h-idx = cong₂ pr (cong nk e) (cong Lset (cong nk e))
  pair : ⟨ pr (nk m) (Lset (nk m)) ∈ˢ seg m ⟩
  pair = finSet-in (suc m) h (pr (nk m) (Lset (nk m))) ∣ idx , h-idx ∣₁

-- The segment satisfies the one-way story.
segStory : (n : ℕ) → LA.aSt1 (seg n)
segStory n = segPair n , (segSingle n , (segZero n , (segDom n , segSucc1 n)))

-- The satisfaction of ψ is built from the meta story.
ψ-in : (x : ⟪ Sset ω ⟫)
     → ∥ Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f)) ∥₁
     → ⟨ (LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ ⟩
ψ-in x = PT.rec (snd ((LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ)) go
  where
  go : Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f))
     → ⟨ (LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ ⟩
  go (f , (st , rg)) = ∣ f , (LA.aSt1-ok f x .snd st , LA.r-ok f x .snd rg) ∣₁

-- Every L-stage below ω is carved.
carve-⊆ : (y : S) → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
        → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
carve-⊆ y = PT.rec (snd (y ∈ˢ LA.U.defSet ψ)) go
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
  go (δ , (δ∈ω , y≡)) = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (sym y≡) (carve δ δ∈ω)
    where
    carve : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟨ Lset δ ∈ˢ LA.U.defSet ψ ⟩
    carve δ δ∈ω = PT.rec (snd (Lset δ ∈ˢ LA.U.defSet ψ)) g δ∈ω
      where
      carve# : (m : ℕ) → ⟨ Lset (nk m) ∈ˢ LA.U.defSet ψ ⟩
      carve# m = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (fm .snd)
        (subst ⟨_⟩ (sym (LA.U.defSet-mem ψ (fm .fst)))
          (ψ-in (fm .fst) ∣ (seg m , seg∈HF m)
            , (segStory m , subst (λ w → w ∈ran seg m) (sym (fm .snd)) (segRan m)) ∣₁))
        where
        fm : Σ[ x ∈ ⟪ Sset ω ⟫ ] (⟪ Sset ω ⟫↪ x ≡ Lset (nk m))
        fm = ∈-asFiber {a = Lset (nk m)} {b = Sset ω} (stage∈HF (nk m) (#∈ω m))
      g : Σ[ m ∈ Lift ℕ ] (nk (lower m) ≡ δ) → ⟨ Lset δ ∈ˢ LA.U.defSet ψ ⟩
      g (m , q) = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (cong Lset q) (carve# (lower m))

-- The family equality, membership-wise: the carve is exactly the stages
-- below ω, in both directions.
family-char : (y : S) → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
            ⟷ ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
family-char y = carve-⊇ y , carve-⊆ y
```

<!--en-->
## The landing and the union assembly

The family `F` is a member of the rud level one ω-block above the running
sup: the full switch discharges it at `(γ ω, ω)`, the arithmetic section
supplying the certificate `ω ∈ γ ω`. The first limit stage is then the
family's union, by the L-tower's union structure in one direction and the
carve in the other, and the rud closure's union operation (`F5`, through
`Jset-rud`) lands the union in the same level. The composition closes
`Q-lim` at the first limit: `Lset ω ∈ Sset (γ ω)`.
<!--zh-->
## 落点与并装配

族 `F` 是运行上确界之上一个 ω 块处的 rud 层的成员：完全切换在 `(γ ω, ω)` 处兑付它，算术节供给证书 `ω ∈ γ ω`。第一个极限阶段于是就是该族的并：一头经 L 塔的并结构，另一头经刻划，而 rud 闭包的并运算 (`F5`，经 `Jset-rud`) 把并送进同一层。复合在第一个极限处闭合 `Q-lim`：`Lset ω ∈ Sset (γ ω)`。
<!--/-->

```agda
-- The family F the carve collects: the L-stages below ω, as a carrier member.
F : S
F = LA.U.defSet ψ

-- The full switch instantiated at the landing pair (γ ω, ω).
module LFS = LimitFullSwitch (γ ω) (γ-lim ω) ω limω ω∈γω

-- The landing: the family is a member of the rud level one ω-block up.
landing : ⟨ F ∈ˢ Sset (γ ω) ⟩
landing = LFS.full-switch-⊇ ψ

-- The first limit stage is the union of the family, both directions.
Lsetω≡⋃F : Lset ω ≡ (⋃ F)
Lsetω≡⋃F = ext-⊆ L⊆⋃F ⋃F⊆L
  where
  L⊆⋃F : Lset ω ⊆ (⋃ F)
  L⊆⋃F x x∈L = PT.rec (snd (x ∈ˢ (⋃ F))) go (Lset-union-limit ω limω x x∈L)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩) → ⟨ x ∈ˢ (⋃ F) ⟩
    go (δ , δ∈ω , x∈Lsuc) = ∈∈ₛ {a = x} {b = ⋃ F} .snd
      (union-ax F x .snd ∣ Lset (sucV δ) , (Lset∈ₛF , x∈ₛLsuc) ∣₁)
      where
      sδ∈ω : ⟨ sucV δ ∈ˢ ω ⟩
      sδ∈ω = limit-succ-mem ω δ limω δ∈ω
      Lset∈F : ⟨ Lset (sucV δ) ∈ˢ F ⟩
      Lset∈F = carve-⊆ (Lset (sucV δ)) ∣ sucV δ , (sδ∈ω , refl) ∣₁
      Lset∈ₛF : ⟨ Lset (sucV δ) ∈ₛ F ⟩
      Lset∈ₛF = ∈∈ₛ {a = Lset (sucV δ)} {b = F} .fst Lset∈F
      x∈ₛLsuc : ⟨ x ∈ₛ Lset (sucV δ) ⟩
      x∈ₛLsuc = ∈∈ₛ {a = x} {b = Lset (sucV δ)} .fst x∈Lsuc
  ⋃F⊆L : (⋃ F) ⊆ Lset ω
  ⋃F⊆L x x∈⋃ = PT.rec (snd (x ∈ˢ Lset ω)) go
    (union-ax F x .fst (∈∈ₛ {a = x} {b = ⋃ F} .fst x∈⋃))
    where
    go : Σ[ f ∈ S ] (⟨ f ∈ₛ F ⟩ × ⟨ x ∈ₛ f ⟩) → ⟨ x ∈ˢ Lset ω ⟩
    go (f , (f∈ₛF , x∈ₛf)) = PT.rec (snd (x ∈ˢ Lset ω)) fStep (carve-⊇ f f∈F)
      where
      f∈F : ⟨ f ∈ˢ F ⟩
      f∈F = ∈∈ₛ {a = f} {b = F} .snd f∈ₛF
      x∈f : ⟨ x ∈ˢ f ⟩
      x∈f = ∈∈ₛ {a = x} {b = f} .snd x∈ₛf
      fStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (f ≡ Lset δ)) → ⟨ x ∈ˢ Lset ω ⟩
      fStep = dStep
        where
        dStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (f ≡ Lset δ)) → ⟨ x ∈ˢ Lset ω ⟩
        dStep (δ , δ∈ω , f≡) = Lset-mono {α = ω} {β = δ} δ∈ω
          (subst (λ w → ⟨ x ∈ˢ w ⟩) f≡ x∈f)

-- The union of the family lands in the same level, by the rud closure's
-- union operation.
⋃F∈Ssetγω : ⟨ (⋃ F) ∈ˢ Sset (γ ω) ⟩
⋃F∈Ssetγω = subst (λ w → ⟨ w ∈ˢ Sset (γ ω) ⟩) (Fof-f5 F F)
  (Jset-rud (γ ω) (γ-lim ω) f5 F F landing landing)

-- Q-lim closes at the first limit.
Q-lim-ω : ⟨ Lset ω ∈ˢ Sset (γ ω) ⟩
Q-lim-ω = subst (λ w → ⟨ w ∈ˢ Sset (γ ω) ⟩) (sym Lsetω≡⋃F) ⋃F∈Ssetγω
```
