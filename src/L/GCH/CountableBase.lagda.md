# The base of the count: the limit stage L_ω is countable, internally

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.CountableBase {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; numeral-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Choice.Finite {ℓ} lem
  using ( Tally; StageOrder; stageOrder; finiteStage )  -- lint-agda: keep (StageOrder used as the projection qualifier)
open import L.Choice.Step {ℓ} lem
  using ( carry; memOf; orderAt; orderAt-step; relOf; birth-mem; module Family )
  renaming ( Mem to MemOf )
open import L.Choice.Table {ℓ} lem using ( Related; IsRel; ixRel-fill; ixRel-rep )
open import L.Choice.Order {ℓ} lem using ( relL; relL-spec )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.GCH.Assembly {ℓ} lem
  using ( StageCountedCoded; inclusion-coded; injl-trans )
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )
open import L.GCH.Pairing {ℓ} lem using ( isL-ord )
open import L.GCH.StageCount {ℓ} lem using ( LimitStageCounted; stage-counted-from )
open import L.InjChain {ℓ} lem using ( ω-limit; finite-excl-ω; pairω; pairω-inj )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; lt; eq; gt ) renaming ( Tri to TriW )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤ )
open import Cubical.Data.FinData.Properties using ( toℕ<n )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier: the ambient membership lives here.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier: `InjL` and the coded injections live here.
module SL = hPropStructure 𝒮ʟ
```

<!--en-->
## No injection of omega into a finite stage
<!--zh-->
## omega 不单射进有穷阶段
<!--/-->

```agda
-- =====================================================================
-- SECTION 1.  A FINITE STAGE HOLDS NO COPY OF omega.
--
--   `L.StageCardinal.FinInj` counts a finite stage against a tally: at
--   every member it picks the least tally index, as a natural number.
--   That number is below the tally's size, so the count lands in the
--   numeral `# size`, and `finite-excl-ω` refutes the composite.  The
--   chapter is imported at omega, where the square law it asks for is
--   `pairω` (src/L/InjChain.lagda.md).
-- =====================================================================

private
  Sq : V ℓ → Type ℓ
  Sq w = Σ[ f ∈ (⟪ w ⟫ × ⟪ w ⟫ → ⟪ w ⟫) ]
           ((x y : ⟪ w ⟫ × ⟪ w ⟫) → f x ≡ f y → x ≡ y)

  sqω : (δ : V ℓ) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ
  sqω δ h ni = subst Sq (sym e) (pairω , pairω-inj)
    where
    e : δ ≡ ω
    e = ∈sucV-elim {A = ω} {x = δ} (setIsSet δ ω) h
          (λ k → Empty.rec (ni k)) (λ q → q)

module SC = L.StageCardinal {ℓ} lem ω ω-ord sqω

private
  module FinNo (n : ℕ) where
    t : Tally (finiteStage n)
    t = StageOrder.tally (stageOrder n)

    open Tally t using ( size )
    module FI = SC.FinInj n t

    noinj : (f : ⟪ ω ⟫ → ⟪ Lset (# n) ⟫)
          → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    noinj f finj = finite-excl-ω (# size) (numeral-ord size) (#∈ω size)
      (λ x → q x , q x) (λ x y e → finj x y (qq x y (cong fst e)))
      where
      vl : ⟪ ω ⟫ → V ℓ
      vl x = ⟪ Lset (# n) ⟫↪ (f x)
      mm : (x : ⟪ ω ⟫) → ⟨ vl x ∈ˢ finiteStage n ⟩
      mm x = member (Lset (# n)) (f x)
      k : ⟪ ω ⟫ → ℕ
      k x = FI.least (vl x) (mm x)
      kb : (x : ⟪ ω ⟫) → k x < size
      kb x = PT.rec isProp≤
        (λ { (i , (pi , _)) → subst (λ w → w < size) pi (toℕ<n i) })
        (FI.least-wit (vl x) (mm x))
      q : ⟪ ω ⟫ → ⟪ # size ⟫
      q x = SQ.FiniteBase.fromFin size (k x , kb x)
      qq : (x y : ⟪ ω ⟫) → q x ≡ q y → f x ≡ f y
      qq x y e = ↪-inj {a = Lset (# n)}
        (FI.h-inj (vl x) (vl y) (mm x) (mm y) (cong SC.numeralω ek))
        where
        ek : k x ≡ k y
        ek = cong fst
          (SQ.FiniteBase.fromFin-inj size (k x , kb x) (k y , kb y) e)

  NoInto : V ℓ → Type ℓ
  NoInto w = (f : ⟪ ω ⟫ → ⟪ Lset w ⟫)
           → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥

  no-inj-fin : (g : V ℓ) → ⟨ g ∈ˢ ω ⟩ → NoInto g
  no-inj-fin g g∈ω = subst NoInto (SC.numeral-wit g g∈ω .snd)
    (FinNo.noinj (SC.numeral-wit g g∈ω .fst))
```

<!--en-->
## The stage order at omega, as a relation of L
<!--zh-->
## omega 处的阶段序，作为 L 的一个关系
<!--/-->

```agda
-- =====================================================================
-- SECTION 2.  L_ω, THE ORDER ON IT AS A SET OF L, AND ITS DOMAIN
-- READING.
--
--   `relL ω` is the stage order at omega, realized as an element of L
--   (src/L/Choice/Order.lagda.md).  `Related` says what its members
--   are: pairs of two members of the stage.  That is the domain
--   hypothesis `OrderType.Code` asks for.
-- =====================================================================

hω : ⟨ isL ω ⟩
hω = isL-ord ω ω-ord

Lω : SL.S
Lω = LsetS ω ω-ord

Rω : SL.S
Rω = relL ω hω ω-ord

specω : IsRel ω Rω
specω = relL-spec ω hω ω-ord

Rsub : (y x : SL.S) → Holds Rω y x
     → ⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩
Rsub y x h = PT.rec isP
  (λ { (_ , h₁) → PT.rec isP
    (λ { (a , h₂) → PT.rec isP
      (λ { (b , (q , _)) →
             subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .fst)) (a .snd)
           , subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .snd)) (b .snd) })
      h₂ })
    h₁ })
  rel
  where
  isP : isProp (⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩)
  isP = isProp× (snd (fst y ∈ˢ Lset ω)) (snd (fst x ∈ˢ Lset ω))
  rel : ⟨ Related ω (pr (fst y) (fst x)) ⟩
  rel = subst (λ w → ⟨ Related ω w ⟩) (prʟ-fst y x)
    (specω (prʟ y x) .fst
      (subst (λ w → ⟨ w ∈ˢ fst Rω ⟩) (sym (prʟ-fst y x)) h))

module OT = Code Lω Rω Rsub

-- The host order at the same presentation, and the two directions
-- between it and the sealed relation of the collapse.
Wω : SWO ⟪ Lset ω ⟫
Wω = carry (Lset ω) (orderAt ω ω-ord)

open SWO Wω using () renaming ( _<∙_ to _<ω_ )

≺→< : (a b : OT.Dom) → a OT.≺ b → a <ω b
≺→< a b k = ixRel-rep ω ω-ord Rω specω a b (OT.≺-out a b k)

<→≺ : (a b : OT.Dom) → a <ω b → a OT.≺ b
<→≺ a b k = OT.≺-in a b (ixRel-fill ω ω-ord Rω specω a b k)

wfω : WellFounded OT._≺_
wfω m = go (SWO.wf∙ Wω m)
  where
  go : {n : OT.Dom} → Acc _<ω_ n → Acc OT._≺_ n
  go {n} (acc r) = acc (λ n' k → go (r n' (≺→< n' n k)))

transω : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
transω {a} {b} {c} k k' =
  <→≺ a c (SWO.trans∙ Wω a b c (≺→< a b k) (≺→< b c k'))

triω : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
triω a b = go (SWO.tri∙ Wω a b)
  where
  go : TriW (a <ω b) (a ≡ b) (b <ω a)
     → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  go (lt h) = inl (<→≺ a b h)
  go (eq e) = inr (inl e)
  go (gt h) = inr (inr (<→≺ b a h))

module C = OT.Conjuncts wfω transω
module I = C.Inj triω
```

<!--en-->
## Every predecessor is born no later
<!--zh-->
## 每个前元的诞生阶段不更晚
<!--/-->

```agda
-- =====================================================================
-- SECTION 3.  THE SEGMENT BELOW A MEMBER SITS IN ONE FINITE STAGE.
--
--   The stage order compares the BIRTH first (src/L/Choice/Step.lagda.md,
--   `Family._≺_`), so a predecessor of x is born at or below the birth
--   of x, hence belongs to the stage one above that birth.  At omega
--   that stage is finite.
-- =====================================================================

private
  module F = Family ω (λ δ _ → orderAt δ) ω-ord

  unfoldω : (a b : MemOf (Lset ω))
          → relOf (orderAt ω ω-ord) a b ≡ F._≺_ a b
  unfoldω a b = cong (λ z → relOf (z ω-ord) a b) (orderAt-step ω)

  bAt : MemOf (Lset ω) → V ℓ
  bAt a = F.bornAt a .fst

  bAt∈ω : (a : MemOf (Lset ω)) → ⟨ bAt a ∈ˢ ω ⟩
  bAt∈ω a = F.bornAt a .snd

  bAt-ord : (a : MemOf (Lset ω)) → IsOrd (bAt a)
  bAt-ord a = mem-ord {A = ω} ω-ord (bAt a) (bAt∈ω a)

  self-at : (a : MemOf (Lset ω)) → ⟨ a .fst ∈ˢ Lset (sucV (bAt a)) ⟩
  self-at a = birth-mem (a .fst) (Lset→isL ω ω-ord (a .fst) (a .snd))

  step-bound : (a b : MemOf (Lset ω)) → F._≺_ a b
             → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
  step-bound a b (inl h) =
    raise (suc∈or≡ (bAt a) (bAt b) (bAt-ord a) (bAt-ord b) h)
    where
    raise : ⟨ sucV (bAt a) ∈ˢ bAt b ⟩ ⊎ (sucV (bAt a) ≡ bAt b)
          → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
    raise (inl k) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (∈sucV-inl {A = bAt b} {x = sucV (bAt a)} k) (self-at a)
    raise (inr e) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (subst (λ w → ⟨ sucV (bAt a) ∈ˢ sucV w ⟩) e (self∈sucV (sucV (bAt a))))
      (self-at a)
  step-bound a b (inr (e , u)) =
    subst (λ w → ⟨ a .fst ∈ˢ Lset (sucV w) ⟩) (sym e) (u .fst)

  atIx : OT.Dom → MemOf (Lset ω)
  atIx m = ⟪ Lset ω ⟫↪ m , memOf (Lset ω) m

  gOf : OT.Dom → V ℓ
  gOf p = sucV (bAt (atIx p))

  gOf∈ω : (p : OT.Dom) → ⟨ gOf p ∈ˢ ω ⟩
  gOf∈ω p = ω-limit (bAt (atIx p)) (bAt∈ω (atIx p))

  seg-bound : (p r : OT.Dom) → r OT.≺ p
            → ⟨ ⟪ Lset ω ⟫↪ r ∈ˢ Lset (gOf p) ⟩
  seg-bound p r k =
    step-bound (atIx r) (atIx p) (transport (unfoldω (atIx r) (atIx p)) (≺→< r p k))
```

<!--en-->
## Every collapse value is a finite ordinal
<!--zh-->
## 每个塌缩值都是有穷序数
<!--/-->

```agda
-- =====================================================================
-- SECTION 4.  THE ORDER TYPE IS INCLUDED IN omega.
--
--   The collapse value at p is the order type of the segment below p.
--   That segment injects, ambiently, into the finite stage of section 3,
--   so omega does not inject into it; and an ordinal that omega does not
--   reach is a member of omega.  This is the shape of `Step.col-fin`
--   (src/L/GCH/Pairing.lagda.md:979).
-- =====================================================================

private
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))

  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ z → isProp× (OT.isProp≺ z p) (setIsSet _ _))
      (I.col-inj r r' (e ∙ sym e'))

  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = PT.rec (isPropSeg p b) (λ z → z) (C.col-out p b h)

col-fin : (p : OT.Dom) → ⟨ C.col p ∈ˢ ω ⟩
col-fin p = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
  where
  refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → Empty.⊥
  refute sub = no-inj-fin (gOf p) (gOf∈ω p) f f-inj
    where
    s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
    s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
    fb : (x : ⟪ ω ⟫)
       → Σ[ m ∈ ⟪ Lset (gOf p) ⟫ ] (⟪ Lset (gOf p) ⟫↪ m ≡ ⟪ Lset ω ⟫↪ (s x .fst))
    fb x = fiber (Lset (gOf p)) (seg-bound p (s x .fst) (s x .snd .fst))
    f : ⟪ ω ⟫ → ⟪ Lset (gOf p) ⟫
    f x = fb x .fst
    f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
    f-inj x y e = ↪-inj {a = ω}
      (sym (s x .snd .snd) ∙ cong C.col rr ∙ s y .snd .snd)
      where
      rr : s x .fst ≡ s y .fst
      rr = ↪-inj {a = Lset ω}
        (sym (fb x .snd) ∙ cong ⟪ Lset (gOf p) ⟫↪ e ∙ fb y .snd)

  go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
  go (inl k) = k
  go (inr (inl e)) =
    Empty.rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
  go (inr (inr ω∈c)) =
    Empty.rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))

otL⊆ω : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ ω ⟩
otL⊆ω z h = PT.rec (snd (z ∈ˢ ω))
  (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ ω ⟩) e (col-fin b) })
  (C.otL-out z h)
```

<!--en-->
## The two theorems
<!--zh-->
## 两条定理
<!--/-->

```agda
-- =====================================================================
-- SECTION 5.  THE PREMISE THE COUNTING CHAPTER LEFT OPEN.
-- =====================================================================

limit-stage-counted : LimitStageCounted
limit-stage-counted =
  injl-trans Lω C.otL ωʟ ∣ C.colTable , I.code ∣₁
    (inclusion-coded C.otL ωʟ otL⊆ω)

stage-counted : StageCountedCoded
stage-counted = stage-counted-from limit-stage-counted
```
