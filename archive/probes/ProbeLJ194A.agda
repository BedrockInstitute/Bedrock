{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.94] probe A: the ambient Hartogs cardinal, ending at the consumer.
--
-- The [LJ-1.90] site (src/ProbeLJ190A.agda:204-211) needs the value
-- `cardκ : IsCardinal κ` (IsCardinal at
-- src/L/BoundedSubset.lagda.md:1045-1046).  The route (LJ-1.91) builds
-- the ambient Hartogs number: the set of order types of well-orders on
-- subsets of ω.  Step 2, the order-type module at a generic SWO
-- carrier, is delivered and measured by src/ProbeLJ192A.agda and is
-- IMPORTED here, not rewritten.
--
-- Steps 1, 3, 4 and 5 are built at the TYPE level rather than through
-- the internal well-order formula: the small type `WO` of well-orders
-- on subsets of ω (step 1), the Hartogs set κ = sett WO ot (step 3),
-- ordinality and the countability facts (step 4), initiality and the
-- supply at the consumer site (step 5).  No internal formula is
-- written and no axiom of choice is used.  LEM enters only through the
-- V-model's impredicativity parameter, which supplies the small
-- classifier Ω' (HPropSmallness); the power set and separation are not
-- used.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lem→impredicativity )
open import Base.Impredicativity using ( HPropSmallness; Impredicativity )

module ProbeLJ194A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; isPropIsTransV; Lset )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; ∅-ord; mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf; module SWO )
open import ProbeLJ192A {ℓ} using ( module OrderType; module Unique )
open import ProbeLJ190A {ℓ} lem using ( module Site )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Functions.Logic as Logic
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit; tt )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Equiv using ( _≃_; equivFun; invEq; secEq; retEq )
open import Cubical.Foundations.Transport using ( substEquiv; transportTransport⁻ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΣ; isPropΠ )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; seteq; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; module WFI )
open import Cubical.Data.Nat using ( ℕ; zero; suc )

open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- the consumer's statement (src/L/BoundedSubset.lagda.md:1045-1046),
-- stated here so the probe does not import the heavy consumer master
IsCardinal : S → Type (ℓ-suc ℓ)
IsCardinal κ = (δ : S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)

-- The ordinal's own strict well-order: the ∈-order on the members of an
-- ordinal.  This is the delivered shape at
-- src/L/StageCardinal.lagda.md:226-258, copied here so that the probe
-- does not import the heavy stage-cardinality chapter (one process,
-- C-12).
module OrdSWO (α : S) (oα : IsOrd α) where

  _≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ n) (m ≡ n) (n ≺ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ˢ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ˢ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ n) (m ≡ n) (n ≺ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ n → n ≺ k → m ≺ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  ordSWO : SWO ⟪ α ⟫
  ordSWO = record
    { _<∙_   = _≺_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- The smallness classifier: LEM redeems the V-model's impredicativity
-- parameter, whose HPropSmallness packs a small type Ω' equivalent to
-- hProp ℓ.  The predicates of a well-order structure live in Ω' so that
-- the structure type stays small (Type ℓ) and can index a sett.
hps : HPropSmallness ℓ
hps = Impredicativity.hPropSmallness (lem→impredicativity lem)

Ω' : Type ℓ
Ω' = hps .fst

dec : Ω' → hProp ℓ
dec = equivFun (hps .snd)

enc : hProp ℓ → Ω'
enc = invEq (hps .snd)

dec∘enc : (P : hProp ℓ) → dec (enc P) ≡ P
dec∘enc = secEq (hps .snd)

-- a helper: transport a decoded truth into the canonical proposition
decEnc : (P : hProp ℓ) → ⟨ dec (enc P) ⟩ → ⟨ P ⟩
decEnc P = transport (cong ⟨_⟩ (dec∘enc P))

encDec : (P : hProp ℓ) → ⟨ P ⟩ → ⟨ dec (enc P) ⟩
encDec P = transport (sym (cong ⟨_⟩ (dec∘enc P)))

-- isSet of the small presentation of a V-set: the presentation embeds
-- into V, and V is a set.
isSet⟪⟫ : (a : S) → isSet (⟪ a ⟫)
isSet⟪⟫ a = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

-- =====================================================================
-- STEP 1: the small type WO of well-orders on subsets of ω.
--
-- A member is (A, R, data): A picks the field, a subset of ω; R is the
-- strict order on the field.  The four laws are stated at the decoded
-- relation on ALL of ⟪ ω ⟫ (stronger than field-restricted, which is
-- what makes the initial segment inherit them), and totality is
-- restricted to the field with UNTRUNCATED field witnesses, so the
-- trichotomy of the decoded SWO needs no choice.
-- =====================================================================
module SmallWO where

  Sub : Type ℓ
  Sub = ⟪ ω ⟫ → Ω'

  car : Sub → Type ℓ
  car A = Σ[ m ∈ ⟪ ω ⟫ ] ⟨ dec (A m) ⟩

  Rel : Type ℓ
  Rel = ⟪ ω ⟫ → ⟪ ω ⟫ → Ω'

  Irr : Rel → Type ℓ
  Irr R = (m : ⟪ ω ⟫) → ⟨ dec (R m m) ⟩ → Empty.⊥

  Trans : Rel → Type ℓ
  Trans R = (m n k : ⟪ ω ⟫) → ⟨ dec (R m n) ⟩ → ⟨ dec (R n k) ⟩ → ⟨ dec (R m k) ⟩

  Wf : Rel → Type ℓ
  Wf R = WellFounded (λ m n → ⟨ dec (R m n) ⟩)

  Total : Sub → Rel → Type ℓ
  Total A R = (m n : ⟪ ω ⟫) → ⟨ dec (A m) ⟩ → ⟨ dec (A n) ⟩
            → (⟨ dec (R m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R n m) ⟩))

  WO : Type ℓ
  WO = Σ[ A ∈ Sub ] Σ[ R ∈ Rel ] (Irr R × Trans R × Wf R × Total A R)

  module Decode (wo : WO) where
    A : Sub
    A = wo .fst

    R : Rel
    R = wo .snd .fst

    D : Irr R × Trans R × Wf R × Total A R
    D = wo .snd .snd

    -- the relation lives one universe up so that the SWO record matches
    -- ProbeLJ192A's ℓₚ (Agda's conversion has no cumulativity)
    _≺_ : car A → car A → Type (ℓ-suc ℓ)
    (m , _) ≺ (n , _) = Lift {ℓ} {ℓ-suc ℓ} (⟨ dec (R m n) ⟩)

    tri≺ : (x y : car A) → Tri (x ≺ y) (x ≡ y) (y ≺ x)
    tri≺ (m , a) (n , b) = go (D .snd .snd .snd m n a b)
      where
      go : (⟨ dec (R m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R n m) ⟩))
         → Tri (Lift {ℓ} {ℓ-suc ℓ} (⟨ dec (R m n) ⟩))
               ((m , a) ≡ (n , b))
               (Lift {ℓ} {ℓ-suc ℓ} (⟨ dec (R n m) ⟩))
      go (inl h) = lt (lift h)
      go (inr (inl e)) = eq (Σ≡Prop {B = λ x → ⟨ dec (A x) ⟩}
        (λ x → snd (dec (A x))) {u = (m , a)} {v = (n , b)} e)
      go (inr (inr h)) = gt (lift h)

    irr≺ : (x : car A) → (x ≺ x → Empty.⊥)
    irr≺ (m , _) (lift h) = D .fst m h

    trans≺ : (x y z : car A) → x ≺ y → y ≺ z → x ≺ z
    trans≺ (m , _) (n , _) (k , _) (lift h) (lift h') = lift (D .snd .fst m n k h h')

    wf≺ : WellFounded _≺_
    wf≺ (m , a) = go m a (D .snd .snd .fst m)
      where
      go : (x : ⟪ ω ⟫) (w : ⟨ dec (A x) ⟩)
         → Acc (λ m n → ⟨ dec (R m n) ⟩) x → Acc _≺_ (x , w)
      go x w (acc rs) = acc (λ { (n , b') (lift h) → go n b' (rs n h) })

    swo : SWO (car A)
    swo = record
      { _<∙_   = _≺_
      ; tri∙   = tri≺
      ; irr∙   = irr≺
      ; trans∙ = trans≺
      ; wf∙    = wf≺ }

  module OT (wo : WO) = OrderType (car (wo .fst)) (Decode.swo wo)

  ot : WO → S
  ot wo = OT.τ wo

  ot-ord : (wo : WO) → IsOrd (ot wo)
  ot-ord wo = OT.τ-ord wo

-- =====================================================================
-- The order type of the ∈-order on an ordinal α is α itself.
-- The collapse of the ∈-order is the identity on the members (one
-- well-founded induction, with the union identity "an ordinal is the
-- union of the successors of its members"), and the union of the
-- successors of all members of α is α.  This is the shared fact the
-- route needs at ω (the natural order's order type is ω) and at κ
-- (the pullback well-order's order type is κ).
-- =====================================================================
module OrdinalSelf (α : S) (oα : IsOrd α) where

  module OO = OrdSWO α oα
  module O = OrderType (⟪ α ⟫) (OO.ordSWO)

  _≺₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  _≺₁_ = OO._≺_

  g : (m : ⟪ α ⟫) → ⟪ α ⟫ → S
  g m r = O.colPick m (λ r _ → O.col r) r (O.≺-dec r m)

  g-inl : (m r : ⟪ α ⟫) (pr : r ≺₁ m) → g m r ≡ sucV (O.col r)
  g-inl m r pr = go (O.≺-dec r m)
    where
    go : (d : (O._≺_ r m) ⊎ ((O._≺_ r m) → Empty.⊥))
       → O.colPick m (λ r _ → O.col r) r d ≡ sucV (O.col r)
    go (inl _) = refl
    go (inr ¬pr) = Empty.rec (¬pr pr)

  g-inr : (m r : ⟪ α ⟫) (¬pr : (r ≺₁ m) → Empty.⊥) → g m r ≡ ∅
  g-inr m r ¬pr = go (O.≺-dec r m)
    where
    go : (d : (O._≺_ r m) ⊎ ((O._≺_ r m) → Empty.⊥))
       → O.colPick m (λ r _ → O.col r) r d ≡ ∅
    go (inl pr) = Empty.rec (¬pr pr)
    go (inr _) = refl

  -- the union identity: an ordinal is the union of the successors of
  -- its members.  All memberships here are the small `∈ₛ` form, which
  -- is what `_⊆_` and `union-ax` speak.
  union-self : (β : S) (oβ : IsOrd β)
             → (⋃ (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)))) ≡ β
  union-self β oβ = extensionality (⋃ (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)))) β
    (fwd , bwd)
    where
    fwd : (x : S) → ⟨ x ∈ₛ (⋃ (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)))) ⟩ → ⟨ x ∈ₛ β ⟩
    fwd x x∈ = PT.rec (snd (x ∈ₛ β)) go1
      (union-ax (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m))) x .fst
        x∈)
      where
      go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)) ⟩ × ⟨ x ∈ₛ v ⟩)
          → ⟨ x ∈ₛ β ⟩
      go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ β)) go2
        (∈∈ₛ {a = v} {b = sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m))} .snd v∈ₛsett)
        where
        go2 : Σ[ m ∈ ⟪ β ⟫ ] (sucV (⟪ β ⟫↪ m) ≡ v) → ⟨ x ∈ₛ β ⟩
        go2 (m , e) = ∈∈ₛ {a = x} {b = β} .fst
          (∈sucV-elim {A = ⟪ β ⟫↪ m} {x = x} (snd (x ∈ˢ β)) x∈sm
            (λ x∈m → oβ .fst {x = ⟪ β ⟫↪ m} {y = x} x∈m (member β m))
            (λ x≡m → subst (λ w → ⟨ w ∈ˢ β ⟩) (sym x≡m) (member β m)))
          where
          x∈sm : ⟨ x ∈ˢ sucV (⟪ β ⟫↪ m) ⟩
          x∈sm = ∈∈ₛ {a = x} {b = sucV (⟪ β ⟫↪ m)} .snd
            (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym e) x∈ₛv)

    bwd : (x : S) → ⟨ x ∈ₛ β ⟩ → ⟨ x ∈ₛ (⋃ (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)))) ⟩
    bwd x x∈β =
      (union-ax (sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m))) x .snd
        ∣ sucV (⟪ β ⟫↪ r) , (w∈ₛsett , x∈ₛs) ∣₁)
      where
      r : ⟪ β ⟫
      r = fiber β {x = x} (∈∈ₛ {a = x} {b = β} .snd x∈β) .fst
      x≡r : ⟪ β ⟫↪ r ≡ x
      x≡r = fiber β {x = x} (∈∈ₛ {a = x} {b = β} .snd x∈β) .snd
      w∈ₛsett : ⟨ sucV (⟪ β ⟫↪ r) ∈ₛ sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m)) ⟩
      w∈ₛsett = ∈∈ₛ {a = sucV (⟪ β ⟫↪ r)} {b = sett (⟪ β ⟫) (λ m → sucV (⟪ β ⟫↪ m))}
        .fst ∣ r , refl ∣₁
      x∈ₛs : ⟨ x ∈ₛ sucV (⟪ β ⟫↪ r) ⟩
      x∈ₛs = ∈∈ₛ {a = x} {b = sucV (⟪ β ⟫↪ r)} .fst
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (cong sucV x≡r)) (self∈sucV x))

  col-self : (m : ⟪ α ⟫) → O.col m ≡ ⟪ α ⟫↪ m
  col-self = WFIα.induction {P = P} step
    where
    module WFIα = Cubical.Induction.WellFounded.WFI (OO.wf₁)
    P : ⟪ α ⟫ → Type (ℓ-suc ℓ)
    P m = O.col m ≡ ⟪ α ⟫↪ m

    step : (m : ⟪ α ⟫) → ((r : ⟪ α ⟫) → r ≺₁ m → P r) → P m
    step m ih = O.col-compute m ∙ union≡member
      where
      union≡member : ⋃ (sett (⟪ α ⟫) (g m)) ≡ ⟪ α ⟫↪ m
      union≡member = extensionality (⋃ (sett (⟪ α ⟫) (g m))) (⟪ α ⟫↪ m) (fwd , bwd)
        where
        fwd : (x : S) → ⟨ x ∈ₛ (⋃ (sett (⟪ α ⟫) (g m))) ⟩ → ⟨ x ∈ₛ ⟪ α ⟫↪ m ⟩
        fwd x x∈ = PT.rec (snd (x ∈ₛ ⟪ α ⟫↪ m)) go1
          (union-ax (sett (⟪ α ⟫) (g m)) x .fst
            x∈)
          where
          go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (⟪ α ⟫) (g m) ⟩ × ⟨ x ∈ₛ v ⟩)
              → ⟨ x ∈ₛ ⟪ α ⟫↪ m ⟩
          go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ ⟪ α ⟫↪ m)) go2
            (∈∈ₛ {a = v} {b = sett (⟪ α ⟫) (g m)} .snd v∈ₛsett)
            where
            go2 : Σ[ r ∈ ⟪ α ⟫ ] (g m r ≡ v) → ⟨ x ∈ₛ ⟪ α ⟫↪ m ⟩
            go2 (r , e) = decide (O.≺-dec r m)
              where
              x∈gr : ⟨ x ∈ₛ g m r ⟩
              x∈gr = subst (λ w → ⟨ x ∈ₛ w ⟩) (sym e) x∈ₛv
              decide : (r ≺₁ m) ⊎ ((r ≺₁ m) → Empty.⊥) → ⟨ x ∈ₛ ⟪ α ⟫↪ m ⟩
              decide (inl pr) = ∈∈ₛ {a = x} {b = ⟪ α ⟫↪ m} .fst
                (∈sucV-elim {A = O.col r} {x = x}
                  (snd (x ∈ˢ ⟪ α ⟫↪ m)) x∈suc
                  (λ x∈colr → OO.ord-inord m .fst {x = ⟪ α ⟫↪ r} {y = x}
                    (subst (λ w → ⟨ x ∈ˢ w ⟩) (ih r pr) x∈colr) pr)
                  (λ x≡colr → subst (λ w → ⟨ w ∈ˢ ⟪ α ⟫↪ m ⟩)
                    (sym (x≡colr ∙ ih r pr)) pr))
                where
                x∈suc : ⟨ x ∈ˢ sucV (O.col r) ⟩
                x∈suc = ∈∈ₛ {a = x} {b = sucV (O.col r)} .snd
                  (subst (λ w → ⟨ x ∈ₛ w ⟩) (g-inl m r pr) x∈gr)
              decide (inr ¬pr) =
                Empty.rec (∅-empty x (subst (λ w → ⟨ x ∈ₛ w ⟩) (g-inr m r ¬pr) x∈gr))

        bwd : (x : S) → ⟨ x ∈ₛ ⟪ α ⟫↪ m ⟩ → ⟨ x ∈ₛ (⋃ (sett (⟪ α ⟫) (g m))) ⟩
        bwd x x∈β =
          union-ax (sett (⟪ α ⟫) (g m)) x .snd
            ∣ sucV (O.col r) , (w∈ₛsett , x∈ₛs) ∣₁
          where
          r : ⟪ α ⟫
          r = fiber α {x = x} (oα .fst {x = ⟪ α ⟫↪ m} {y = x}
            (∈∈ₛ {a = x} {b = ⟪ α ⟫↪ m} .snd x∈β) (member α m)) .fst
          x≡r : ⟪ α ⟫↪ r ≡ x
          x≡r = fiber α {x = x} (oα .fst {x = ⟪ α ⟫↪ m} {y = x}
            (∈∈ₛ {a = x} {b = ⟪ α ⟫↪ m} .snd x∈β) (member α m)) .snd
          r≺m : r ≺₁ m
          r≺m = subst (λ w → ⟨ w ∈ˢ ⟪ α ⟫↪ m ⟩) (sym x≡r)
            (∈∈ₛ {a = x} {b = ⟪ α ⟫↪ m} .snd x∈β)
          w∈ₛsett : ⟨ sucV (O.col r) ∈ₛ sett (⟪ α ⟫) (g m) ⟩
          w∈ₛsett = ∈∈ₛ {a = sucV (O.col r)} {b = sett (⟪ α ⟫) (g m)}
            .fst ∣ r , g-inl m r r≺m ∣₁
          x∈ₛs : ⟨ x ∈ₛ sucV (O.col r) ⟩
          x∈ₛs = ∈∈ₛ {a = x} {b = sucV (O.col r)} .fst
            (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (cong sucV (ih r r≺m ∙ x≡r)))
              (self∈sucV x))

  ot-self : O.τ ≡ α
  ot-self = cong (⋃_) (seteq (⟪ α ⟫) (⟪ α ⟫)
              (λ m → sucV (O.col m)) (λ m → sucV (⟪ α ⟫↪ m))
              ( (λ m → ∣ m , cong sucV (sym (col-self m)) ∣₁)
              , (λ m → ∣ m , cong sucV (col-self m) ∣₁) ))
          ∙ union-self α oα

-- =====================================================================
-- The natural well-order on ω, as a member of WO, with order type ω.
-- The carrier is all of ⟪ ω ⟫ (the field is the trivial predicate), the
-- order is the ∈-order on the numerals, and the order type is ω by the
-- isomorphism to OrdSWO ω plus ordinal-self.
-- =====================================================================
module Natural where

  open SmallWO

  ⊤-hProp : hProp ℓ
  ⊤-hProp = Logic.⊤ {ℓ}

  A₀ : Sub
  A₀ _ = enc ⊤-hProp

  m∈n : ⟪ ω ⟫ → ⟪ ω ⟫ → hProp ℓ
  m∈n m n = (⟪ ω ⟫↪ m ∈ₛ ⟪ ω ⟫↪ n)

  R₀ : Rel
  R₀ m n = enc (m∈n m n)

  irr₀ : Irr R₀
  irr₀ m h = ∈-irrefl (⟪ ω ⟫↪ m)
    (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ m} .snd (decEnc (m∈n m m) h))

  trans₀ : Trans R₀
  trans₀ m n k h h' =
    encDec (m∈n m k) (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ k} .fst
      ((mem-ord {A = ω} ω-ord (⟪ ω ⟫↪ k) (member ω k)) .fst
        (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ n} .snd (decEnc (m∈n m n) h))
        (∈∈ₛ {a = ⟪ ω ⟫↪ n} {b = ⟪ ω ⟫↪ k} .snd (decEnc (m∈n n k) h'))))

  wf₀ : Wf R₀
  wf₀ m = go m (regularityV (⟪ ω ⟫↪ m))
    where
    go : (x : ⟪ ω ⟫) → Acc _∈ᵗ_ (⟪ ω ⟫↪ x) → Acc (λ m n → ⟨ dec (R₀ m n) ⟩) x
    go x (acc rs) = acc (λ n h →
      go n (rs (⟪ ω ⟫↪ n) (∈∈ₛ {a = ⟪ ω ⟫↪ n} {b = ⟪ ω ⟫↪ x} .snd
        (decEnc (m∈n n x) h))))

  total₀ : Total A₀ R₀
  total₀ m n a b = go (ord-tri (⟪ ω ⟫↪ m) (mem-ord {A = ω} ω-ord (⟪ ω ⟫↪ m) (member ω m))
                               (⟪ ω ⟫↪ n) (mem-ord {A = ω} ω-ord (⟪ ω ⟫↪ n) (member ω n)))
    where
    go : (⟨ ⟪ ω ⟫↪ m ∈ˢ ⟪ ω ⟫↪ n ⟩
          ⊎ ((⟪ ω ⟫↪ m ≡ ⟪ ω ⟫↪ n) ⊎ ⟨ ⟪ ω ⟫↪ n ∈ˢ ⟪ ω ⟫↪ m ⟩))
       → (⟨ dec (R₀ m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R₀ n m) ⟩))
    go (inl h) = inl (encDec (m∈n m n) (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ n} .fst h))
    go (inr (inl p)) = inr (inl (↪-inj {a = ω} p))
    go (inr (inr h)) = inr (inr (encDec (m∈n n m) (∈∈ₛ {a = ⟪ ω ⟫↪ n} {b = ⟪ ω ⟫↪ m} .fst h)))

  wo₀ : WO
  wo₀ = A₀ , R₀ , irr₀ , trans₀ , wf₀ , total₀

  module O0 = Decode wo₀
  module OS = OrdSWO ω ω-ord
  module U0 = Unique (car A₀) (⟪ ω ⟫) (O0.swo) (OS.ordSWO)

  opaque
    fwd : car A₀ → ⟪ ω ⟫
    fwd (m , _) = m

    bwd : ⟪ ω ⟫ → car A₀
    bwd m = m , encDec ⊤-hProp (lift tt)

    f-mono : {x y : car A₀} → x O0.≺ y → fwd x OS.≺ fwd y
    f-mono {m , _} {n , _} (lift h) =
      ∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ n} .snd (decEnc (m∈n m n) h)

    f-mono-bwd : {x y : car A₀} → fwd x OS.≺ fwd y → x O0.≺ y
    f-mono-bwd {m , _} {n , _} h = lift (encDec (m∈n m n)
      (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ⟪ ω ⟫↪ n} .fst h))

    f-surj : (y : ⟪ ω ⟫) → ∥ Σ[ x ∈ car A₀ ] (fwd x ≡ y) ∥₁
    f-surj m = ∣ (m , encDec ⊤-hProp (lift tt)) , refl ∣₁

  iso₀ : U0.OrderIso
  iso₀ = record
    { f          = fwd
    ; f-mono     = f-mono
    ; f-mono-bwd = f-mono-bwd
    ; f-surj     = f-surj }

  module UU = U0.Uniq iso₀
  module OSω = OrdinalSelf ω ω-ord

  ot₀≡ω : ot wo₀ ≡ ω
  ot₀≡ω = UU.τ-eq ∙ OSω.ot-self

-- =====================================================================
-- Countability: for every wo, its order type injects into ω.  The
-- reverse collapse, from a member b of the order type to the carrier
-- element p with col p ≡ b, is the least such p in the well-order
-- (leastOf, the delivered LEM-priced search).  The carrier injects into
-- ⟪ ω ⟫ by the field projection.
-- =====================================================================
module Count (wo : SmallWO.WO) where

  open SmallWO
  module O = OT wo
  module D = Decode wo

  A : Sub
  A = wo .fst

  P : (b : S) → car A → hProp (ℓ-suc ℓ)
  P b p = ((O.col p ≡ b) , setIsSet _ _)

  nonempty : (b : S) → ⟨ b ∈ˢ O.τ ⟩ → ∥ Σ[ p ∈ car A ] ⟨ P b p ⟩ ∥₁
  nonempty b b∈ = O.col-surj b b∈

  least : (b : S) → ⟨ b ∈ˢ O.τ ⟩ → car A
  least b b∈ = fst (leastOf (D.swo) lem (P b) (nonempty b b∈))

  least-wit : (b : S) (b∈ : ⟨ b ∈ˢ O.τ ⟩) → O.col (least b b∈) ≡ b
  least-wit b b∈ = leastOf (D.swo) lem (P b) (nonempty b b∈) .snd .fst

  j : ⟪ O.τ ⟫ → car A
  j m = least (⟪ O.τ ⟫↪ m) (member O.τ m)

  j-inj : (m n : ⟪ O.τ ⟫) → j m ≡ j n → m ≡ n
  j-inj m n e = ↪-inj {a = O.τ}
    (sym (least-wit (⟪ O.τ ⟫↪ m) (member O.τ m))
      ∙ cong (O.col) e
      ∙ least-wit (⟪ O.τ ⟫↪ n) (member O.τ n))

  proj : car A → ⟪ ω ⟫
  proj (m , _) = m

  proj-inj : (x y : car A) → proj x ≡ proj y → x ≡ y
  proj-inj (m , a) (n , b) e =
    Σ≡Prop {B = λ x → ⟨ dec (A x) ⟩} (λ x → snd (dec (A x)))
      {u = (m , a)} {v = (n , b)} e

  count : ⟪ O.τ ⟫ ↪ ⟪ ω ⟫
  count = (λ m → proj (j m)) , λ m n e → j-inj m n (proj-inj (j m) (j n) e)

-- the same injection, transported along an equality ot wo ≡ δ, so that
-- a member of κ (which is a set of order types) is directly countable
countAt : (wo : SmallWO.WO) (δ : S) (e : SmallWO.ot wo ≡ δ) → ⟪ δ ⟫ ↪ ⟪ ω ⟫
countAt wo δ e = f , inj
  where
  e' : ⟪ δ ⟫ ≃ ⟪ SmallWO.ot wo ⟫
  e' = substEquiv (λ α → ⟪ α ⟫) (sym e)
  f : ⟪ δ ⟫ → ⟪ ω ⟫
  f m = Count.count wo .fst (equivFun e' m)
  inj : (x y : ⟪ δ ⟫) → f x ≡ f y → x ≡ y
  inj x y h =
    sym (retEq e' x) ∙ cong (invEq e') (Count.count wo .snd (equivFun e' x) (equivFun e' y) h)
      ∙ retEq e' y

-- =====================================================================
-- The initial segment: for p in the carrier of wo, the well-order
-- restricted to { q : q ≺ p } is again a member of WO, and its order
-- type is col p.  The field of the segment is the subset of ω picked by
-- A m × (m R m₀) with m₀ = p .fst; the order is R with the right
-- argument in the segment.  This is the closure under initial segments
-- that makes the Hartogs set transitive.
-- =====================================================================
module InitialSegment (wo : SmallWO.WO) (p : SmallWO.car (wo .fst)) where

  open SmallWO
  module O = OT wo
  module D = Decode wo

  A : Sub
  A = wo .fst

  R : Rel
  R = wo .snd .fst

  D4 : Irr R × Trans R × Wf R × Total A R
  D4 = wo .snd .snd

  m₀ : ⟪ ω ⟫
  m₀ = p .fst

  Q : ⟪ ω ⟫ → hProp ℓ
  Q m = ((⟨ dec (A m) ⟩ × ⟨ dec (R m m₀) ⟩)
        , isProp× (snd (dec (A m))) (snd (dec (R m m₀))))

  Aₚ : Sub
  Aₚ m = enc (Q m)

  Q' : ⟪ ω ⟫ → ⟪ ω ⟫ → hProp ℓ
  Q' m n = ((⟨ dec (R m n) ⟩ × ⟨ dec (R n m₀) ⟩)
           , isProp× (snd (dec (R m n))) (snd (dec (R n m₀))))

  Rₚ : Rel
  Rₚ m n = enc (Q' m n)

  irrₚ : Irr Rₚ
  irrₚ m h = D4 .fst m (decEnc (Q' m m) h .fst)

  transₚ : Trans Rₚ
  transₚ m n k h h' = encDec (Q' m k)
    ( D4 .snd .fst m n k (decEnc (Q' m n) h .fst) (decEnc (Q' n k) h' .fst)
    , decEnc (Q' n k) h' .snd )

  wfₚ : Wf Rₚ
  wfₚ m = go m (D4 .snd .snd .fst m)
    where
    go : (x : ⟪ ω ⟫) → Acc (λ m n → ⟨ dec (R m n) ⟩) x
       → Acc (λ m n → ⟨ dec (Rₚ m n) ⟩) x
    go x (acc rs) = acc (λ n h → go n (rs n (decEnc (Q' n x) h .fst)))

  totalₚ : Total Aₚ Rₚ
  totalₚ m n a b = go (D4 .snd .snd .snd m n (decEnc (Q m) a .fst) (decEnc (Q n) b .fst))
    where
    go : (⟨ dec (R m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R n m) ⟩))
       → (⟨ dec (Rₚ m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (Rₚ n m) ⟩))
    go (inl h) = inl (encDec (Q' m n) (h , decEnc (Q n) b .snd))
    go (inr (inl e)) = inr (inl e)
    go (inr (inr h)) = inr (inr (encDec (Q' n m) (h , decEnc (Q m) a .snd)))

  woₚ : WO
  woₚ = Aₚ , Rₚ , irrₚ , transₚ , wfₚ , totalₚ

  module Oₚ = OT woₚ
  module Dₚ = Decode woₚ

  forget : car Aₚ → car A
  forget (m , w) = (m , decEnc (Q m) w .fst)

  -- the segment witness for an element already in the field below p
  seg-wit : (m : ⟪ ω ⟫) (a : ⟨ dec (A m) ⟩) → ⟨ dec (R m m₀) ⟩ → ⟨ dec (Aₚ m) ⟩
  seg-wit m a h = encDec (Q m) (a , h)

  -- the segment witness for an element below p
  seg : (n : ⟪ ω ⟫) (a' : ⟨ dec (A n) ⟩) (h : ⟨ dec (R n m₀) ⟩) → ⟨ dec (Aₚ n) ⟩
  seg n a' h = encDec (Q n) (a' , h)

  forget-spec : (r : car A) (w' : ⟨ dec (Aₚ (r .fst)) ⟩)
              → (r .fst , decEnc (Q (r .fst)) w' .fst) ≡ r
  forget-spec (n , a') w' = Σ≡Prop {B = λ x → ⟨ dec (A x) ⟩}
    (λ x → snd (dec (A x)))
    {u = (n , decEnc (Q n) w' .fst)} {v = (n , a')} refl

  gₚ : (x : car Aₚ) → car Aₚ → S
  gₚ x r = Oₚ.colPick x (λ r _ → Oₚ.col r) r (Oₚ.≺-dec r x)

  g : (x : car A) → car A → S
  g x r = O.colPick x (λ r _ → O.col r) r (O.≺-dec r x)

  gₚ-inl : (x r : car Aₚ) (pr : r Dₚ.≺ x) → gₚ x r ≡ sucV (Oₚ.col r)
  gₚ-inl x r pr = go (Oₚ.≺-dec r x)
    where
    go : (d : (r Dₚ.≺ x) ⊎ ((r Dₚ.≺ x) → Empty.⊥))
       → Oₚ.colPick x (λ r _ → Oₚ.col r) r d ≡ sucV (Oₚ.col r)
    go (inl _) = refl
    go (inr ¬pr) = Empty.rec (¬pr pr)

  gₚ-inr : (x r : car Aₚ) (¬pr : (r Dₚ.≺ x) → Empty.⊥) → gₚ x r ≡ ∅
  gₚ-inr x r ¬pr = go (Oₚ.≺-dec r x)
    where
    go : (d : (r Dₚ.≺ x) ⊎ ((r Dₚ.≺ x) → Empty.⊥))
       → Oₚ.colPick x (λ r _ → Oₚ.col r) r d ≡ ∅
    go (inl pr) = Empty.rec (¬pr pr)
    go (inr _) = refl

  g-inl : (x r : car A) (pr : r D.≺ x) → g x r ≡ sucV (O.col r)
  g-inl x r pr = go (O.≺-dec r x)
    where
    go : (d : (r D.≺ x) ⊎ ((r D.≺ x) → Empty.⊥))
       → O.colPick x (λ r _ → O.col r) r d ≡ sucV (O.col r)
    go (inl _) = refl
    go (inr ¬pr) = Empty.rec (¬pr pr)

  g-inr : (x r : car A) (¬pr : (r D.≺ x) → Empty.⊥) → g x r ≡ ∅
  g-inr x r ¬pr = go (O.≺-dec r x)
    where
    go : (d : (r D.≺ x) ⊎ ((r D.≺ x) → Empty.⊥))
       → O.colPick x (λ r _ → O.col r) r d ≡ ∅
    go (inl pr) = Empty.rec (¬pr pr)
    go (inr _) = refl

  -- the collapse of the segment is the collapse of the original order
  colₚ-self : (x : car Aₚ) → Oₚ.col x ≡ O.col (forget x)
  colₚ-self = WFIα.induction {P = P} step
    where
    module WFIα = Cubical.Induction.WellFounded.WFI (Dₚ.wf≺)
    P : car Aₚ → Type (ℓ-suc ℓ)
    P x = Oₚ.col x ≡ O.col (forget x)
    step : (x : car Aₚ) → ((r : car Aₚ) → r Dₚ.≺ x → P r) → P x
    step (m , w) ih = Oₚ.col-compute (m , w) ∙ union-eq ∙ sym (O.col-compute (m , a))
      where
      a : ⟨ dec (A m) ⟩
      a = decEnc (Q m) w .fst
      wp : ⟨ dec (R m m₀) ⟩
      wp = decEnc (Q m) w .snd

      -- x ∈ sucV (col (forget r)) for r ≺ p gives x ∈ col p's family
      via-suc : (x : S) (r : car A) (pr : r D.≺ (m , a))
              → ⟨ x ∈ˢ sucV (O.col r) ⟩ → ⟨ x ∈ˢ (⋃ (sett (car A) (g (m , a)))) ⟩
      via-suc x r pr x∈suc = ∈∈ₛ {a = x} {b = (⋃ (sett (car A) (g (m , a))))} .snd
        (union-ax (sett (car A) (g (m , a))) x .snd
          ∣ sucV (O.col r)
          , ( ∈∈ₛ {a = sucV (O.col r)} {b = sett (car A) (g (m , a))} .fst
              ∣ r , g-inl (m , a) r pr ∣₁
            , ∈∈ₛ {a = x} {b = sucV (O.col r)} .fst x∈suc ) ∣₁)

      -- x ∈ sucV (colₚ r) for r ≺ₚ (m, w) gives x ∈ colₚ (m, w)'s family
      via-sucₚ : (x : S) (r : car Aₚ) (pr : r Dₚ.≺ (m , w))
               → ⟨ x ∈ˢ sucV (Oₚ.col r) ⟩ → ⟨ x ∈ˢ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
      via-sucₚ x r pr x∈suc = ∈∈ₛ {a = x} {b = (⋃ (sett (car Aₚ) (gₚ (m , w))))} .snd
        (union-ax (sett (car Aₚ) (gₚ (m , w))) x .snd
          ∣ sucV (Oₚ.col r)
          , ( ∈∈ₛ {a = sucV (Oₚ.col r)} {b = sett (car Aₚ) (gₚ (m , w))} .fst
              ∣ r , gₚ-inl (m , w) r pr ∣₁
            , ∈∈ₛ {a = x} {b = sucV (Oₚ.col r)} .fst x∈suc ) ∣₁)

      -- decoding helpers for the order relation
      n≺m : (n : ⟪ ω ⟫) (w' : ⟨ dec (Aₚ n) ⟩)
          → (n , w') Dₚ.≺ (m , w)
          → (n , decEnc (Q n) w' .fst) D.≺ (m , a)
      n≺m n w' pr = lift (decEnc (Q' n m) (lower pr) .fst)

      -- the segment witness for an element below m, via transitivity
      seg-step : (n : ⟪ ω ⟫) (a' : ⟨ dec (A n) ⟩) → ⟨ dec (R n m) ⟩ → ⟨ dec (Aₚ n) ⟩
      seg-step n a' h = seg n a' (D4 .snd .fst n m m₀ h wp)

      union-eq : ⋃ (sett (car Aₚ) (gₚ (m , w))) ≡ ⋃ (sett (car A) (g (m , a)))
      union-eq = extensionality (⋃ (sett (car Aₚ) (gₚ (m , w)))) (⋃ (sett (car A) (g (m , a))))
        (fwd , bwd)
        where
        fwd : (x : S) → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
             → ⟨ x ∈ₛ (⋃ (sett (car A) (g (m , a)))) ⟩
        fwd x x∈ = PT.rec (snd (x ∈ₛ (⋃ (sett (car A) (g (m , a)))))) go1
          (union-ax (sett (car Aₚ) (gₚ (m , w))) x .fst x∈)
          where
          go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (car Aₚ) (gₚ (m , w)) ⟩ × ⟨ x ∈ₛ v ⟩)
              → ⟨ x ∈ₛ (⋃ (sett (car A) (g (m , a)))) ⟩
          go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ (⋃ (sett (car A) (g (m , a)))))) go2
            (∈∈ₛ {a = v} {b = sett (car Aₚ) (gₚ (m , w))} .snd v∈ₛsett)
            where
            go2 : Σ[ r ∈ car Aₚ ] (gₚ (m , w) r ≡ v) → ⟨ x ∈ₛ (⋃ (sett (car A) (g (m , a)))) ⟩
            go2 (r , e) = decide (Oₚ.≺-dec r (m , w))
              where
              x∈gr : ⟨ x ∈ₛ gₚ (m , w) r ⟩
              x∈gr = subst (λ z → ⟨ x ∈ₛ z ⟩) (sym e) x∈ₛv
              decide : (r Dₚ.≺ (m , w)) ⊎ ((r Dₚ.≺ (m , w)) → Empty.⊥)
                     → ⟨ x ∈ₛ (⋃ (sett (car A) (g (m , a)))) ⟩
              decide (inl pr) = ∈∈ₛ {a = x} {b = (⋃ (sett (car A) (g (m , a))))} .fst
                (∈sucV-elim {A = Oₚ.col r} {x = x}
                  (snd (x ∈ˢ (⋃ (sett (car A) (g (m , a)))))) x∈sucₚ
                  (λ x∈colr → via-suc x (forget r) (n≺m (r .fst) (r .snd) pr)
                    (∈sucV-inl {A = O.col (forget r)} {x = x}
                      (subst (λ z → ⟨ x ∈ˢ z ⟩) (ih r pr) x∈colr)))
                  (λ x≡colr → via-suc x (forget r) (n≺m (r .fst) (r .snd) pr)
                    (subst (λ z → ⟨ z ∈ˢ sucV (O.col (forget r)) ⟩)
                      (sym (x≡colr ∙ ih r pr)) (self∈sucV (O.col (forget r))))))
                where
                x∈sucₚ : ⟨ x ∈ˢ sucV (Oₚ.col r) ⟩
                x∈sucₚ = ∈∈ₛ {a = x} {b = sucV (Oₚ.col r)} .snd
                  (subst (λ z → ⟨ x ∈ₛ z ⟩) (gₚ-inl (m , w) r pr) x∈gr)
              decide (inr ¬pr) =
                Empty.rec (∅-empty x (subst (λ z → ⟨ x ∈ₛ z ⟩) (gₚ-inr (m , w) r ¬pr) x∈gr))

        bwd : (x : S) → ⟨ x ∈ₛ (⋃ (sett (car A) (g (m , a)))) ⟩
             → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
        bwd x x∈ = PT.rec (snd (x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))))) go1
          (union-ax (sett (car A) (g (m , a))) x .fst x∈)
          where
          go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (car A) (g (m , a)) ⟩ × ⟨ x ∈ₛ v ⟩)
              → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
          go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))))) go2
            (∈∈ₛ {a = v} {b = sett (car A) (g (m , a))} .snd v∈ₛsett)
            where
            go2 : Σ[ r ∈ car A ] (g (m , a) r ≡ v) → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
            go2 (r , e) = decide (O.≺-dec r (m , a))
              where
              x∈gr : ⟨ x ∈ₛ g (m , a) r ⟩
              x∈gr = subst (λ z → ⟨ x ∈ₛ z ⟩) (sym e) x∈ₛv
              decide : (r D.≺ (m , a)) ⊎ ((r D.≺ (m , a)) → Empty.⊥)
                     → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (gₚ (m , w)))) ⟩
              decide (inl pr) = ∈∈ₛ {a = x} {b = (⋃ (sett (car Aₚ) (gₚ (m , w))))} .fst
                (∈sucV-elim {A = O.col r} {x = x}
                  (snd (x ∈ˢ (⋃ (sett (car Aₚ) (gₚ (m , w)))))) x∈suc
                  (λ x∈colr → via-sucₚ x rₚ prₚ
                    (∈sucV-inl {A = Oₚ.col rₚ} {x = x}
                      (subst (λ z → ⟨ x ∈ˢ z ⟩) (sym hint) x∈colr)))
                  (λ x≡colr → via-sucₚ x rₚ prₚ
                    (subst (λ z → ⟨ z ∈ˢ sucV (Oₚ.col rₚ) ⟩)
                      (sym (x≡colr ∙ sym hint)) (self∈sucV (Oₚ.col rₚ)))))
                where
                x∈suc : ⟨ x ∈ˢ sucV (O.col r) ⟩
                x∈suc = ∈∈ₛ {a = x} {b = sucV (O.col r)} .snd
                  (subst (λ z → ⟨ x ∈ₛ z ⟩) (g-inl (m , a) r pr) x∈gr)
                rₚ : car Aₚ
                rₚ = (r .fst , seg-step (r .fst) (r .snd) (lower pr))
                prₚ : rₚ Dₚ.≺ (m , w)
                prₚ = lift (encDec (Q' (r .fst) m) (lower pr , wp))
                hint : Oₚ.col rₚ ≡ O.col r
                hint = ih rₚ prₚ ∙ cong (O.col) (forget-spec r (rₚ .snd))
              decide (inr ¬pr) =
                Empty.rec (∅-empty x (subst (λ z → ⟨ x ∈ₛ z ⟩) (g-inr (m , a) r ¬pr) x∈gr))

  -- the order type of the segment is col p
  otₚ≡colp : ot woₚ ≡ O.col p
  otₚ≡colp = cong (⋃_) (seteq (car Aₚ) (car Aₚ)
              (λ x → sucV (Oₚ.col x)) (λ x → sucV (O.col (forget x)))
              ( (λ x → ∣ x , cong sucV (sym (colₚ-self x)) ∣₁)
              , (λ x → ∣ x , cong sucV (colₚ-self x) ∣₁) ))
          ∙ seg-union
    where
    -- ⋃ (sett (car Aₚ) (λ x → sucV (col (forget x)))) ≡ col p
    seg-union : ⋃ (sett (car Aₚ) (λ x → sucV (O.col (forget x)))) ≡ O.col p
    seg-union = extensionality (⋃ (sett (car Aₚ) (λ x → sucV (O.col (forget x))))) (O.col p)
      (fwd , bwd)
      where
      fwd : (x : S) → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))) ⟩ → ⟨ x ∈ₛ O.col p ⟩
      fwd x x∈ = PT.rec (snd (x ∈ₛ O.col p)) go1
        (union-ax (sett (car Aₚ) (λ y → sucV (O.col (forget y)))) x .fst x∈)
        where
        go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (car Aₚ) (λ y → sucV (O.col (forget y))) ⟩ × ⟨ x ∈ₛ v ⟩)
            → ⟨ x ∈ₛ O.col p ⟩
        go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ O.col p)) go2
          (∈∈ₛ {a = v} {b = sett (car Aₚ) (λ y → sucV (O.col (forget y)))} .snd v∈ₛsett)
          where
          go2 : Σ[ y ∈ car Aₚ ] (sucV (O.col (forget y)) ≡ v) → ⟨ x ∈ₛ O.col p ⟩
          go2 (y , e) = subst (λ z → ⟨ x ∈ₛ z ⟩) (sym (O.col-compute p))
            (union-ax (sett (car A) (g p)) x .snd
              ∣ sucV (O.col (forget y))
              , ( ∈∈ₛ {a = sucV (O.col (forget y))} {b = sett (car A) (g p)} .fst
                  ∣ forget y , g-inl p (forget y) (lift (decEnc (Q (y .fst)) (y .snd) .snd)) ∣₁
                , ∈∈ₛ {a = x} {b = sucV (O.col (forget y))} .fst
                    (subst (λ z → ⟨ x ∈ˢ z ⟩) (sym e)
                      (∈∈ₛ {a = x} {b = v} .snd x∈ₛv)) ) ∣₁)
      bwd : (x : S) → ⟨ x ∈ₛ O.col p ⟩ → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))) ⟩
      bwd x x∈ = PT.rec (snd (x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))))) go1
        (union-ax (sett (car A) (g p)) x .fst
          (subst (λ z → ⟨ x ∈ₛ z ⟩) (O.col-compute p) x∈))
        where
        go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (car A) (g p) ⟩ × ⟨ x ∈ₛ v ⟩)
            → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))) ⟩
        go1 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))))) go2
          (∈∈ₛ {a = v} {b = sett (car A) (g p)} .snd v∈ₛsett)
          where
          go2 : Σ[ r ∈ car A ] (g p r ≡ v) → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))) ⟩
          go2 (r , e) = decide (O.≺-dec r p)
            where
            x∈gr : ⟨ x ∈ₛ g p r ⟩
            x∈gr = subst (λ z → ⟨ x ∈ₛ z ⟩) (sym e) x∈ₛv
            decide : (r D.≺ p) ⊎ ((r D.≺ p) → Empty.⊥)
                   → ⟨ x ∈ₛ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))) ⟩
            decide (inl pr) = ∈∈ₛ {a = x} {b = (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y)))))} .fst
              (∈sucV-elim {A = O.col r} {x = x}
                (snd (x ∈ˢ (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y))))))) x∈suc
                (λ x∈colr → ∈∈ₛ {a = x} {b = (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y)))))} .snd
                  (union-ax (sett (car Aₚ) (λ y → sucV (O.col (forget y)))) x .snd
                    ∣ sucV (O.col r) , ( ∈∈ₛ {a = sucV (O.col r)} {b = sett (car Aₚ) (λ y → sucV (O.col (forget y)))} .fst
                        ∣ (r .fst , seg (r .fst) (r .snd) (lower pr))
                        , cong (λ z → sucV (O.col z)) (forget-spec r (seg (r .fst) (r .snd) (lower pr))) ∣₁
                      , ∈∈ₛ {a = x} {b = sucV (O.col r)} .fst
                          (∈sucV-inl {A = O.col r} {x = x} x∈colr) ) ∣₁))
                (λ x≡colr → ∈∈ₛ {a = x} {b = (⋃ (sett (car Aₚ) (λ y → sucV (O.col (forget y)))))} .snd
                  (union-ax (sett (car Aₚ) (λ y → sucV (O.col (forget y)))) x .snd
                    ∣ sucV (O.col r) , ( ∈∈ₛ {a = sucV (O.col r)} {b = sett (car Aₚ) (λ y → sucV (O.col (forget y)))} .fst
                        ∣ (r .fst , seg (r .fst) (r .snd) (lower pr))
                        , cong (λ z → sucV (O.col z)) (forget-spec r (seg (r .fst) (r .snd) (lower pr))) ∣₁
                      , ∈∈ₛ {a = x} {b = sucV (O.col r)} .fst
                          (subst (λ z → ⟨ z ∈ˢ sucV (O.col r) ⟩) (sym x≡colr) (self∈sucV (O.col r))) ) ∣₁)))
              where
              x∈suc : ⟨ x ∈ˢ sucV (O.col r) ⟩
              x∈suc = ∈∈ₛ {a = x} {b = sucV (O.col r)} .snd
                (subst (λ z → ⟨ x ∈ₛ z ⟩) (g-inl p r pr) x∈gr)
            decide (inr ¬pr) =
              Empty.rec (∅-empty x (subst (λ z → ⟨ x ∈ₛ z ⟩) (g-inr p r ¬pr) x∈gr))

-- =====================================================================
-- STEP 3: the Hartogs set κ = { ot wo : wo ∈ WO }, with its ordinality
-- (transitivity via the initial segment) and ω ∈ κ.
-- =====================================================================
module Hartogs where

  open SmallWO

  κ : S
  κ = sett WO ot

  ω∈κ : ⟨ ω ∈ˢ κ ⟩
  ω∈κ = ∣ Natural.wo₀ , Natural.ot₀≡ω ∣₁

  κ-mem : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → ∥ Σ[ wo ∈ WO ] (ot wo ≡ δ) ∥₁
  κ-mem δ δ∈ = δ∈

  -- a member of an order type is itself an order type (the initial
  -- segment below the collapsing element)
  member-of-ot : (wo : WO) (x : S) → ⟨ x ∈ˢ ot wo ⟩ → ⟨ x ∈ˢ κ ⟩
  member-of-ot wo x x∈ = go1 (∈∈ₛ {a = x} {b = ot wo} .fst x∈)
    where
    module O = OT wo
    A : Sub
    A = wo .fst
    go1 : ⟨ x ∈ₛ ot wo ⟩ → ⟨ x ∈ˢ κ ⟩
    go1 x∈ = PT.rec (snd (x ∈ˢ κ)) go2
      (union-ax (sett (car A) (λ p → sucV (O.col p))) x .fst x∈)
      where
      go2 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (car A) (λ p → sucV (O.col p)) ⟩ × ⟨ x ∈ₛ v ⟩)
          → ⟨ x ∈ˢ κ ⟩
      go2 (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ κ)) go3
        (∈∈ₛ {a = v} {b = sett (car A) (λ p → sucV (O.col p))} .snd v∈ₛsett)
        where
        go3 : Σ[ p ∈ car A ] (sucV (O.col p) ≡ v) → ⟨ x ∈ˢ κ ⟩
        go3 (p , e) = ∈sucV-elim {A = O.col p} {x = x} (snd (x ∈ˢ κ)) x∈suc
          (λ x∈colp → PT.rec (snd (x ∈ˢ κ)) go4
            (O.col-img p x x∈colp))
          (λ x≡colp → ∣ InitialSegment.woₚ wo p
            , InitialSegment.otₚ≡colp wo p ∙ sym x≡colp ∣₁)
          where
          x∈suc : ⟨ x ∈ˢ sucV (O.col p) ⟩
          x∈suc = ∈∈ₛ {a = x} {b = sucV (O.col p)} .snd
            (subst (λ z → ⟨ x ∈ₛ z ⟩) (sym e) x∈ₛv)
          go4 : Σ[ q ∈ car A ] (O.col q ≡ x) → ⟨ x ∈ˢ κ ⟩
          go4 (q , h) = ∣ InitialSegment.woₚ wo q
            , InitialSegment.otₚ≡colp wo q ∙ h ∣₁

  κ-trans : {x δ : S} → ⟨ x ∈ˢ δ ⟩ → ⟨ δ ∈ˢ κ ⟩ → ⟨ x ∈ˢ κ ⟩
  κ-trans {x} {δ} x∈δ δ∈κ = PT.rec (snd (x ∈ˢ κ)) go (κ-mem δ δ∈κ)
    where
    go : Σ[ wo ∈ WO ] (ot wo ≡ δ) → ⟨ x ∈ˢ κ ⟩
    go (wo , e) = member-of-ot wo x (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym e) x∈δ)

  ordκ : IsOrd κ
  ordκ = trans , mems
    where
    trans : isTransV κ
    trans {x} {y} y∈x x∈κ = κ-trans {x = y} {δ = x} y∈x x∈κ
    mems : (z : S) → ⟨ z ∈ˢ κ ⟩ → isTransV z
    mems z z∈κ = PT.rec (isPropIsTransV z) (λ { (wo , e) →
      subst IsOrd e (ot-ord wo) .fst }) (κ-mem z z∈κ)

  module OK = OrdSWO κ ordκ

  -- =================================================================
  -- The pullback: an injection κ ↪ ω gives a well-order on a subset
  -- of ω with order type κ.  Its field is the image of the injection
  -- and its order is the pullback of the ∈-order on κ.
  -- =================================================================
  module Pullback (g : ⟪ κ ⟫ ↪ ⟪ ω ⟫) where

    f : ⟪ κ ⟫ → ⟪ ω ⟫
    f = g .fst

    f-inj : (x y : ⟪ κ ⟫) → f x ≡ f y → x ≡ y
    f-inj = g .snd

    Q : ⟪ ω ⟫ → hProp ℓ
    Q m = (Σ[ k ∈ ⟪ κ ⟫ ] (f k ≡ m)) , isPropQ m
      where
      isPropQ : (m : ⟪ ω ⟫) → isProp (Σ[ k ∈ ⟪ κ ⟫ ] (f k ≡ m))
      isPropQ m (k , p) (k' , p') = Σ≡Prop {B = λ x → f x ≡ m}
        (λ x → isSet⟪⟫ ω (f x) m) (f-inj k k' (p ∙ sym p'))

    A' : Sub
    A' m = enc (Q m)

    P-body : ⟪ ω ⟫ → ⟪ ω ⟫ → Type ℓ
    P-body m n = Σ[ k ∈ ⟪ κ ⟫ ] Σ[ k' ∈ ⟪ κ ⟫ ]
      ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ κ ⟫↪ k ∈ₛ ⟪ κ ⟫↪ k' ⟩))

    P : ⟪ ω ⟫ → ⟪ ω ⟫ → hProp ℓ
    P m n = (P-body m n , isPropP m n)
      where
      isPropP : (m n : ⟪ ω ⟫)
              → isProp (Σ[ k ∈ ⟪ κ ⟫ ] Σ[ k' ∈ ⟪ κ ⟫ ]
                ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ κ ⟫↪ k ∈ₛ ⟪ κ ⟫↪ k' ⟩)))
      isPropP m n (k , w) (k' , w') =
        Σ≡Prop {B = λ x → Σ[ k₂ ∈ ⟪ κ ⟫ ]
                  ((f x ≡ m) × ((f k₂ ≡ n) × ⟨ ⟪ κ ⟫↪ x ∈ₛ ⟪ κ ⟫↪ k₂ ⟩))}
          (λ x → isPropRest x)
          (f-inj k k' (w .snd .fst ∙ sym (w' .snd .fst)))
        where
        isPropRest : (x : ⟪ κ ⟫)
                   → isProp (Σ[ k₂ ∈ ⟪ κ ⟫ ]
                       ((f x ≡ m) × ((f k₂ ≡ n) × ⟨ ⟪ κ ⟫↪ x ∈ₛ ⟪ κ ⟫↪ k₂ ⟩)))
        isPropRest x (k₂ , u) (k₂' , u') =
          Σ≡Prop {B = λ y → (f x ≡ m) × ((f y ≡ n) × ⟨ ⟪ κ ⟫↪ x ∈ₛ ⟪ κ ⟫↪ y ⟩)}
            (λ y → isProp× (isSet⟪⟫ ω (f x) m)
              (isProp× (isSet⟪⟫ ω (f y) n)
                (snd (⟪ κ ⟫↪ x ∈ₛ ⟪ κ ⟫↪ y))))
            (f-inj k₂ k₂' (u .snd .fst ∙ sym (u' .snd .fst)))

    R' : Rel
    R' m n = enc (P m n)

    irr' : Irr R'
    irr' m h = ∈-irrefl (⟪ κ ⟫↪ k)
      (subst (λ z → ⟨ ⟪ κ ⟫↪ k ∈ˢ z ⟩)
        (sym (cong (⟪ κ ⟫↪) (f-inj k k' (p ∙ sym p'))))
        (∈∈ₛ {a = ⟪ κ ⟫↪ k} {b = ⟪ κ ⟫↪ k'} .snd h₁))
      where
      w = decEnc (P m m) h
      k : ⟪ κ ⟫
      k = w .fst
      k' : ⟪ κ ⟫
      k' = w .snd .fst
      p : f k ≡ m
      p = w .snd .snd .fst
      p' : f k' ≡ m
      p' = w .snd .snd .snd .fst
      h₁ : ⟨ ⟪ κ ⟫↪ k ∈ₛ ⟪ κ ⟫↪ k' ⟩
      h₁ = w .snd .snd .snd .snd

    trans' : Trans R'
    trans' m n k h h' =
      encDec (P m k) ( k₁ , k₃ , p₁ , p₃ , trans₁' h₁ h₂' )
      where
      w = decEnc (P m n) h
      w' = decEnc (P n k) h'
      k₁ : ⟪ κ ⟫
      k₁ = w .fst
      k₂ : ⟪ κ ⟫
      k₂ = w .snd .fst
      k₂' : ⟪ κ ⟫
      k₂' = w' .fst
      k₃ : ⟪ κ ⟫
      k₃ = w' .snd .fst
      p₁ : f k₁ ≡ m
      p₁ = w .snd .snd .fst
      p₂ : f k₂ ≡ n
      p₂ = w .snd .snd .snd .fst
      p₂' : f k₂' ≡ n
      p₂' = w' .snd .snd .fst
      p₃ : f k₃ ≡ k
      p₃ = w' .snd .snd .snd .fst
      h₁ : ⟨ ⟪ κ ⟫↪ k₁ ∈ₛ ⟪ κ ⟫↪ k₂ ⟩
      h₁ = w .snd .snd .snd .snd
      h₂ : ⟨ ⟪ κ ⟫↪ k₂' ∈ₛ ⟪ κ ⟫↪ k₃ ⟩
      h₂ = w' .snd .snd .snd .snd
      k₂≡k₂' : k₂ ≡ k₂'
      k₂≡k₂' = f-inj k₂ k₂' (p₂ ∙ sym p₂')
      h₂' : ⟨ ⟪ κ ⟫↪ k₂ ∈ₛ ⟪ κ ⟫↪ k₃ ⟩
      h₂' = subst (λ z → ⟨ ⟪ κ ⟫↪ z ∈ₛ ⟪ κ ⟫↪ k₃ ⟩) (sym k₂≡k₂') h₂
      trans₁' : ⟨ ⟪ κ ⟫↪ k₁ ∈ₛ ⟪ κ ⟫↪ k₂ ⟩
              → ⟨ ⟪ κ ⟫↪ k₂ ∈ₛ ⟪ κ ⟫↪ k₃ ⟩
              → ⟨ ⟪ κ ⟫↪ k₁ ∈ₛ ⟪ κ ⟫↪ k₃ ⟩
      trans₁' a b = ∈∈ₛ {a = ⟪ κ ⟫↪ k₁} {b = ⟪ κ ⟫↪ k₃} .fst
        (OK.trans₁ k₁ k₂ k₃
          (∈∈ₛ {a = ⟪ κ ⟫↪ k₁} {b = ⟪ κ ⟫↪ k₂} .snd a)
          (∈∈ₛ {a = ⟪ κ ⟫↪ k₂} {b = ⟪ κ ⟫↪ k₃} .snd b))

    wf' : Wf R'
    wf' m = acc (λ n h → step n h)
      where
      acc-map : (y : ⟪ κ ⟫) → Acc OK._≺_ y → Acc (λ m n → ⟨ dec (R' m n) ⟩) (f y)
      acc-map y (acc rs) = acc (λ n h → step₂ n h)
        where
        step₂ : (n : ⟪ ω ⟫) → ⟨ dec (R' n (f y)) ⟩
              → Acc (λ m n → ⟨ dec (R' m n) ⟩) n
        step₂ n h = subst (λ z → Acc (λ m n → ⟨ dec (R' m n) ⟩) z)
          p₂ (acc-map k₂ (rs k₂ h₂'))
          where
          w = decEnc (P n (f y)) h
          k₂ : ⟪ κ ⟫
          k₂ = w .fst
          k₃ : ⟪ κ ⟫
          k₃ = w .snd .fst
          p₂ : f k₂ ≡ n
          p₂ = w .snd .snd .fst
          p₃ : f k₃ ≡ f y
          p₃ = w .snd .snd .snd .fst
          h₂ : ⟨ ⟪ κ ⟫↪ k₂ ∈ₛ ⟪ κ ⟫↪ k₃ ⟩
          h₂ = w .snd .snd .snd .snd
          h₂' : k₂ OK.≺ y
          h₂' = ∈∈ₛ {a = ⟪ κ ⟫↪ k₂} {b = ⟪ κ ⟫↪ y} .snd
            (subst (λ z → ⟨ ⟪ κ ⟫↪ k₂ ∈ₛ ⟪ κ ⟫↪ z ⟩) (f-inj k₃ y p₃) h₂)
      step : (n : ⟪ ω ⟫) → ⟨ dec (R' n m) ⟩ → Acc (λ m n → ⟨ dec (R' m n) ⟩) n
      step n h = subst (λ z → Acc (λ m n → ⟨ dec (R' m n) ⟩) z)
        p₂ (acc-map k₂ (OK.wf₁ k₂))
        where
        w = decEnc (P n m) h
        k₂ : ⟪ κ ⟫
        k₂ = w .fst
        p₂ : f k₂ ≡ n
        p₂ = w .snd .snd .fst

    total' : Total A' R'
    total' m n a b = go (unwrap (OK.tri₁ k k'))
      where
      w = decEnc (Q m) a
      w' = decEnc (Q n) b
      k : ⟪ κ ⟫
      k = w .fst
      k' : ⟪ κ ⟫
      k' = w' .fst
      p : f k ≡ m
      p = w .snd
      p' : f k' ≡ n
      p' = w' .snd
      unwrap : (t : Tri (k OK.≺ k') (k ≡ k') (k' OK.≺ k))
             → (⟨ ⟪ κ ⟫↪ k ∈ˢ ⟪ κ ⟫↪ k' ⟩ ⊎ ((k ≡ k') ⊎ ⟨ ⟪ κ ⟫↪ k' ∈ˢ ⟪ κ ⟫↪ k ⟩))
      unwrap (lt h) = inl h
      unwrap (eq e) = inr (inl e)
      unwrap (gt h) = inr (inr h)
      go : (⟨ ⟪ κ ⟫↪ k ∈ˢ ⟪ κ ⟫↪ k' ⟩
            ⊎ ((k ≡ k') ⊎ ⟨ ⟪ κ ⟫↪ k' ∈ˢ ⟪ κ ⟫↪ k ⟩))
         → (⟨ dec (R' m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R' n m) ⟩))
      go (inl h) = inl (encDec (P m n)
        (k , k' , p , p' , ∈∈ₛ {a = ⟪ κ ⟫↪ k} {b = ⟪ κ ⟫↪ k'} .fst h))
      go (inr (inl e)) = inr (inl
        (subst (λ z → z ≡ n) p (cong (f) e ∙ p')))
      go (inr (inr h)) = inr (inr (encDec (P n m)
        (k' , k , p' , p , ∈∈ₛ {a = ⟪ κ ⟫↪ k'} {b = ⟪ κ ⟫↪ k} .fst h)))

    wo' : WO
    wo' = A' , R' , irr' , trans' , wf' , total'

    module D' = Decode wo'
    module U' = Unique (car A') (⟪ κ ⟫) (D'.swo) (OK.ordSWO)

    g-fwd : car A' → ⟪ κ ⟫
    g-fwd (m , a) = decEnc (Q m) a .fst

    g-bwd : ⟪ κ ⟫ → car A'
    g-bwd k = (f k , encDec (Q (f k)) (k , refl))

    opaque
      g-mono : {x y : car A'} → x D'.≺ y → g-fwd x OK.≺ g-fwd y
      g-mono {m , a} {n , b} (lift h) = go (decEnc (P m n) h)
        where
        go : Σ[ k ∈ ⟪ κ ⟫ ] Σ[ k' ∈ ⟪ κ ⟫ ]
               ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ κ ⟫↪ k ∈ₛ ⟪ κ ⟫↪ k' ⟩))
           → ⟨ ⟪ κ ⟫↪ (g-fwd (m , a)) ∈ˢ ⟪ κ ⟫↪ (g-fwd (n , b)) ⟩
        go (k , k' , p₁ , p₂ , h₀) =
          ∈∈ₛ {a = ⟪ κ ⟫↪ (g-fwd (m , a))} {b = ⟪ κ ⟫↪ (g-fwd (n , b))} .snd
            (subst (λ z → ⟨ ⟪ κ ⟫↪ (g-fwd (m , a)) ∈ₛ ⟪ κ ⟫↪ z ⟩) (k'≡g' k' p₂)
              (subst (λ z → ⟨ ⟪ κ ⟫↪ z ∈ₛ ⟪ κ ⟫↪ k' ⟩) (k≡g k p₁) h₀))
          where
          k≡g : (k : ⟪ κ ⟫) → f k ≡ m → k ≡ g-fwd (m , a)
          k≡g k p = f-inj k (g-fwd (m , a)) (p ∙ sym (decEnc (Q m) a .snd))
          k'≡g' : (k' : ⟪ κ ⟫) → f k' ≡ n → k' ≡ g-fwd (n , b)
          k'≡g' k' p = f-inj k' (g-fwd (n , b)) (p ∙ sym (decEnc (Q n) b .snd))

      g-mono-bwd : {x y : car A'} → g-fwd x OK.≺ g-fwd y → x D'.≺ y
      g-mono-bwd {m , a} {n , b} h = lift (encDec (P m n)
        ( g-fwd (m , a)
        , ( g-fwd (n , b)
          , ( decEnc (Q m) a .snd
            , ( decEnc (Q n) b .snd
              , ∈∈ₛ {a = ⟪ κ ⟫↪ (g-fwd (m , a))} {b = ⟪ κ ⟫↪ (g-fwd (n , b))} .fst h )))))

      g-surj : (y : ⟪ κ ⟫) → ∥ Σ[ x ∈ car A' ] (g-fwd x ≡ y) ∥₁
      g-surj y = ∣ g-bwd y , cong fst rt ∣₁
        where
        rt : decEnc (Q (f y)) (encDec (Q (f y)) (y , refl)) ≡ (y , refl)
        rt = transportTransport⁻ (cong ⟨_⟩ (dec∘enc (Q (f y)))) (y , refl)

    iso' : U'.OrderIso
    iso' = record
      { f          = g-fwd
      ; f-mono     = g-mono
      ; f-mono-bwd = g-mono-bwd
      ; f-surj     = g-surj }

    module UU' = U'.Uniq iso'
    module OSκ = OrdinalSelf κ ordκ

    ot'≡κ : ot wo' ≡ κ
    ot'≡κ = UU'.τ-eq ∙ OSκ.ot-self

  -- STEP 5: initiality.  An injection κ ↪ δ for δ ∈ κ gives κ ↪ ω by
  -- composition with countability, then the pullback puts κ itself into
  -- κ, contradicting regularity.
  cardκ : IsCardinal κ
  cardκ δ δ∈κ inj = PT.rec (isProp⊥) go (κ-mem δ δ∈κ) inj
    where
    isProp⊥ : isProp (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)
    isProp⊥ = isPropΠ (λ _ → λ { () })
    go : Σ[ wo ∈ WO ] (ot wo ≡ δ) → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)
    go (wo , e) inj' = ∈-irrefl κ κ∈κ
      where
      countδ : ⟪ δ ⟫ ↪ ⟪ ω ⟫
      countδ = countAt wo δ e
      g : ⟪ κ ⟫ ↪ ⟪ ω ⟫
      g = (λ m → fst countδ (fst inj' m))
        , (λ m n h → snd inj' m n (snd countδ (fst inj' m) (fst inj' n) h))
      κ∈κ : ⟨ κ ∈ˢ κ ⟩
      κ∈κ = ∣ Pullback.wo' g , Pullback.ot'≡κ g ∣₁

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω h = ∈-irrefl ω (ω-ord .fst {x = κ} {y = ω} ω∈κ h)

-- =====================================================================
-- STEP 5 (the supply): the [LJ-1.90] site shape
-- (src/ProbeLJ190A.agda:204-211), with the Hartogs cardinal in the κ
-- slot.  The Site machinery (lam, ordλ, succλ, x ∈ Lset lam,
-- AllCodes A ∈ Lset lam) is the delivered generic module from the
-- LJ-1.90 probe, instantiated at A = Lset ω, α = ω.
-- =====================================================================
module SiteAt where

  module S0 = Site (LsetS ω ω-ord) ω ω-ord (∈-irrefl ω)

  κ : S
  κ = Hartogs.κ

  ordκ : IsOrd κ
  ordκ = Hartogs.ordκ

  cardκ : IsCardinal κ
  cardκ = Hartogs.cardκ

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω = Hartogs.κ∉ω

  α : S
  α = ω

  ordα : IsOrd α
  ordα = ω-ord

  α∈κ : ⟨ α ∈ˢ κ ⟩
  α∈κ = Hartogs.ω∈κ

  α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥
  α∉ω = ∈-irrefl ω

  x : S
  x = ∅

  x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩
  x⊆Lα = S0.x⊆Lα

  lam : S
  lam = S0.lam

  ordλ : IsOrd lam
  ordλ = S0.ordλ

  α∈λ : ⟨ α ∈ˢ lam ⟩
  α∈λ = S0.α∈λ

  succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
  succλ = S0.succλ

  x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩
  x∈Lλ = S0.x∈Lλ
