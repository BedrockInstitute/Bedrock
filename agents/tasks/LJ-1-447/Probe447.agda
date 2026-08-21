{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.447] PROBE.  The descent split at BOTH least cardinals.
--
--   W3 FIRST  `both-in-suc`.  Typechecked ALONE, obligation omitted.
--
--   TERM      `descent-both`.  Four-case split: coded membership
--             (case 4 paid), both equal (case 3 paid), coded equal
--             and ambient a member (vacuous under residue).
--
--   Ambient seal: five projections, Probe437.agda:90-107.
--   Coded selection: Probe431.agda:108-131, nonempty-coded a
--   module hypothesis, κC sealed at the export.  Do not import a
--   probe.  init-at-kappa, descent-case4-coded and descent-data
--   are module hypotheses at the types their probes delivered.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-447.Probe447 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square; ordSWO )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode; module LeastCardInjL )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  isL-ord, sealed.  Same one line as Probe437.agda:67-69.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- W2.  The successor split, once, at a generic member of sucV x.
-- Instantiated at κL and at κC.  Shape of Probe421.agda:185-204.
in-suc-decides :
    (x : V ℓ) (ox : IsOrd x) (d : V ℓ) (od : IsOrd d)
  → ⟨ d ∈ sucV x ⟩
  → (d ≡ x) ⊎ ⟨ d ∈ x ⟩
in-suc-decides x ox d od d∈suc = go (ord-tri d od x ox)
  where
  go : ⟨ d ∈ x ⟩ ⊎ ((d ≡ x) ⊎ ⟨ x ∈ d ⟩)
     → (d ≡ x) ⊎ ⟨ d ∈ x ⟩
  go (inl d∈x) = inr d∈x
  go (inr (inl d≡x)) = inl d≡x
  go (inr (inr x∈d)) = Empty.rec*
    (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* d∈suc cycle self)
    where
    cycle : ⟨ d ∈ x ⟩ → Empty.⊥* {ℓ-suc ℓ}
    cycle d∈x = lift (∈-irrefl x (ox .fst x∈d d∈x))
    self : d ≡ x → Empty.⊥* {ℓ-suc ℓ}
    self d≡x = lift (∈-irrefl x (subst (λ w → ⟨ x ∈ w ⟩) d≡x x∈d))

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- FIVE projections, Probe437.agda:90-107.  This site does not
-- re-measure the wall.
-- =====================================================================

opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ∈sucL : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ sucV (fst a) ⟩
  κ∈sucL a oa = LeastCardInjL.κ∈sα a oa

  κ-injL : (a : S) (oa : IsOrd (fst a))
         → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  κ-injL a oa = LeastCardInjL.κ-inj a oa

  κ-min-atL : (a : S) (oa : IsOrd (fst a))
            → (δ : S) → ⟨ fst δ ∈ˢ fst (κL a oa) ⟩
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-atL a oa = LeastCardInjL.κ-min-at a oa

-- =====================================================================
-- The coded selection, rebuilt from Probe431.agda:108-131.
-- Generic in the bound γ.  nonempty-coded is a module hypothesis.
-- κC is sealed at the export so fst κC is an atom (P-i, R-36).
-- =====================================================================

module _ (γ : V ℓ) (oγ : IsOrd γ) where

  upγ : Mem (Lset γ) → S
  upγ (x , m) = x , Lset→isL γ oγ x m

  hSucα : (a : S) (oa : IsOrd (fst a)) → ⟨ isL (sucV (fst a)) ⟩
  hSucα a oa =
    Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
      (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : (a : S) (oa : IsOrd (fst a)) → ⟪ sucV (fst a) ⟫ → S
  upα a oa m = ⟪ sucV (fst a) ⟫↪ m
             , isL-trans (member (sucV (fst a)) m) (hSucα a oa)

  CodedInjP' : (a : S) (oa : IsOrd (fst a))
             → ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' a oa d =
    ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα a oa d) ∥₁ , squash₁

  module _
    (nonempty-coded :
        (a : S) (oa : IsOrd (fst a))
      → ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' a oa d ⟩ ∥₁)
    where

    module Sel (a : S) (oa : IsOrd (fst a)) where

      opaque
        w : SWO (⟪ sucV (fst a) ⟫)
        w = ordSWO (sucV (fst a)) (suc-ord oa)

      selected : Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w (CodedInjP' a oa) d
      selected = leastOf w lem (CodedInjP' a oa) (nonempty-coded a oa)

      raw : S
      raw = upα a oa (fst selected)

      raw∈suc : ⟨ fst raw ∈ sucV (fst a) ⟩
      raw∈suc = member (sucV (fst a)) (fst selected)

    opaque
      κC : (a : S) (oa : IsOrd (fst a)) → S
      κC a oa = Sel.raw a oa

      κC∈suc : (a : S) (oa : IsOrd (fst a))
             → ⟨ fst (κC a oa) ∈ sucV (fst a) ⟩
      κC∈suc a oa = Sel.raw∈suc a oa

    -- =================================================================
    -- W3.  both-in-suc.  Obligation omitted.  The two halves sit over
    -- the same sucV x: left is κ∈sucL, right is κC∈suc.
    -- =================================================================

    both-in-suc :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ sucV x ⟩
        × ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ sucV x ⟩
    both-in-suc x ox _ = κ∈sucL a ox , κC∈suc a ox
      where
      a : S
      a = x , isL-ord x ox

    -- Probe430.agda:96-98, restated at the sealed κC.  Needed for
    -- in-suc-decides at the coded cardinal.
    κC-ord : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κC a oa))
    κC-ord a oa = mem-ord {A = sucV (fst a)} (suc-ord oa) (fst (κC a oa))
                    (κC∈suc a oa)

    -- =================================================================
    -- THE OBLIGATION.  Module hypotheses at the types the GO probes
    -- delivered.  residue is an argument, not inhabited.
    -- =================================================================

    module _
      (init-at-kappa :
          (a : S) (oa : IsOrd (fst a))
        → ⟨ ω ∈ˢ fst (κL a oa) ⟩
        → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
             → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
        → Init (fst (κL a oa)))
      (descent-case4-coded :
          (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
        → ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ x ⟩
        → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
        → sq x)
      (descent-data :
          (x d : S) (ox : IsOrd (fst x))
        → ⟨ fst d ∈ˢ fst x ⟩
        → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
        → sq (fst d)
        → sq (fst x))
      where

      descent-both :
          (residue : (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
                   → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
                   → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩)
        → (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
        → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
        → sq x
      descent-both residue x ox ω∈x ih =
        splitC (in-suc-decides x ox (fst κc) oκc (κC∈suc a ox))
        where
        a : S
        a = x , isL-ord x ox
        κc : S
        κc = κC a ox
        oκc : IsOrd (fst κc)
        oκc = κC-ord a ox
        κl : S
        κl = κL a ox
        oκl : IsOrd (fst κl)
        oκl = κoL a ox

        ω∈κl : fst κl ≡ x → ⟨ ω ∈ˢ fst κl ⟩
        ω∈κl κl≡x = subst (λ w → ⟨ ω ∈ˢ w ⟩) (sym κl≡x) ω∈x

        members : fst κl ≡ x
                → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κl ⟩
                → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
        members κl≡x β oβ β∈κ infβ =
          ∣ ih β (subst (λ w → ⟨ β ∈ˢ w ⟩) κl≡x β∈κ) oβ infβ ∣₁

        by-init : fst κl ≡ x → sq x
        by-init κl≡x =
          subst sq κl≡x
            (via-col-square (fst κl)
              (init-at-kappa a ox (ω∈κl κl≡x) (members κl≡x)))

        vacuous : fst κc ≡ x → ⟨ fst κl ∈ x ⟩ → sq x
        vacuous κc≡x κl∈x = Empty.rec (∈-irrefl x x∈x)
          where
          κc∈x : ⟨ fst κc ∈ˢ x ⟩
          κc∈x = residue x ox ω∈x κl∈x
          x∈x : ⟨ x ∈ˢ x ⟩
          x∈x = subst (λ w → ⟨ w ∈ˢ x ⟩) κc≡x κc∈x

        splitC : (fst κc ≡ x) ⊎ ⟨ fst κc ∈ x ⟩ → sq x
        splitC (inr κc∈x) = descent-case4-coded x ox ω∈x κc∈x ih
        splitC (inl κc≡x) = splitL (in-suc-decides x ox (fst κl) oκl (κ∈sucL a ox))
          where
          splitL : (fst κl ≡ x) ⊎ ⟨ fst κl ∈ x ⟩ → sq x
          splitL (inl κl≡x) = by-init κl≡x
          splitL (inr κl∈x) = vacuous κc≡x κl∈x
