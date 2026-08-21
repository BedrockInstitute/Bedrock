{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.486]  W3 FIRST, then the obligation.
-- The bound the rank carve has never had.  PairBound at two sets.
-- Rebuilds the rank at [LJ-1.416]'s type.  Does not import a probe.
-- Does not carve.  Does not build any InjCode conjunct.
--
-- W3 FIRST  `fits`.  PairBound a C, type only.  Obligation omitted.
-- TERM       `rank-bound`.  The unique bound of those pairs.
--
-- [LJ-1.417]'s bounding ordinal rebuilt as boundingOrd on that rank,
-- not imported.  isL-ord rebuilt, opaque (P-i).  OrdSWO rebuilt at
-- StageCardinal's type so oa supplies w.  Do not import a probe.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.  Nothing lands in src/.
-- Do not postulate.  Do not widen the bound to a class.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-486.Probe486 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( boundingOrd; ∅-ord; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

-- =====================================================================
-- W3.  PairBound's telescope against the rank's.  Application only.
-- Obligation omitted.  Rank omitted.  InjCode omitted.
--
-- PairBound (D C : S) at src/L/InjChain.lagda.md:276-277.
-- Two 𝒮ʟ-sets.  below at :299-300 is a pair of a member of D with
-- a member of C.  The rank's pairs are (m, rank m) across two sets.
-- InclGraph's pairs are (x, x) at one set
-- (src/L/InjChain.lagda.md:584-589).  That is a different device.
-- C-42: the identity-pair site does not transfer.
-- =====================================================================

module W3 (a C : S) where
  module PB = PairBound a C

  fits : S
  fits = PB.bnd

-- =====================================================================
-- Rank, rebuilt at [LJ-1.416]'s delivered type.  Probe416.agda:38-78.
-- Swo-rank-mono is not spent: boundingOrd wants the family and IsOrd.
-- =====================================================================

module Rank {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  RankAt : A → Type (ℓ-suc ℓ)
  RankAt _ = Σ[ ρ ∈ V ℓ ] IsOrd ρ

  predAt : (a b : A)
         → Tri (b <∙ a) (b ≡ a) (a <∙ b)
         → ((x : A) → x <∙ a → RankAt x)
         → RankAt b
  predAt a b (lt h) ih = ih b h
  predAt a b (eq _) _  = ∅ , ∅-ord
  predAt a b (gt _) _  = ∅ , ∅-ord

  pred : (a : A) → ((b : A) → b <∙ a → RankAt b) → (b : A) → RankAt b
  pred a ih b = predAt a b (tri∙ b a) ih

  go : (a : A) → Acc _<∙_ a → RankAt a
  go a (acc rs) = bnd .fst , bnd .snd .fst
    where
    ih : (x : A) → x <∙ a → RankAt x
    ih x h = go x (rs x h)
    bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)

  swo-rank : A → V ℓ
  swo-rank a = go a (wf∙ a) .fst

  swo-rank-ord : (a : A) → IsOrd (swo-rank a)
  swo-rank-ord a = go a (wf∙ a) .snd

swo-rank : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
swo-rank w = Rank.swo-rank w

swo-rank-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A) → IsOrd (swo-rank w a)
swo-rank-ord w = Rank.swo-rank-ord w

-- =====================================================================
-- The wrap PairBound wants and the rank does not supply.
-- Sealed: the body is ∈-induction via ord∈Lset-suc
-- (src/L/SquareLawClosed.lagda.md:46-52).  Rebuilt.  Not imported.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- =====================================================================
-- The ordinal well-order, rebuilt at StageCardinal's OrdSWO
-- (src/L/StageCardinal.lagda.md:228-264).  oa supplies w.
-- =====================================================================

module OrdSWO (α : V ℓ) (oα : IsOrd α) where

  _≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ n) (m ≡ n) (n ≺ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ ⟪ α ⟫↪ m ⟩))
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

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = record
    { _<∙_   = _≺_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- =====================================================================
-- Obligation.  [LJ-1.417]'s bounding ordinal as boundingOrd on the
-- rebuilt rank (Probe417.agda:83-89), wrapped by isL-ord, then
-- PairBound.  fiber converts m : S to ⟪ fst a ⟫.  Do not carve.
-- =====================================================================

rank-bound :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (swo-rank (OrdSWO.w (fst a) oa)
                                 (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
rank-bound a oa = PB.bnd , below
  where
  w = OrdSWO.w (fst a) oa
  pack = boundingOrd ⟪ fst a ⟫ (swo-rank w) (swo-rank-ord w)
  β = pack .fst
  oβ = pack .snd .fst
  C : S
  C = β , isL-ord β oβ
  module PB = PairBound a C
  below : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (swo-rank w (fiber (fst a) mx .fst)) ∈ fst PB.bnd ⟩
  below m mx = PB.below m z mx r∈β
    where
    k = fiber (fst a) mx .fst
    r = swo-rank w k
    r∈β : ⟨ r ∈ β ⟩
    r∈β = pack .snd .snd k
    z : S
    z = r , isL-trans {x = β} {y = r} r∈β (snd C)
