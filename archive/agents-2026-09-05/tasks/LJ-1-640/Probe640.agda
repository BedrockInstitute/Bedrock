{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.640]  IS THE BILL'S SITE A LEAST-CARDINAL SITE?
--
-- THE OBLIGATION.  `bill-site-is-least`, section 3.
--
-- Nothing lands in src/.  No square law is built and NO CONJUNCT 4 IS
-- BUILT: no type in this file names `Init`, `Init4` or `sq`.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.
--
-- THE MODULE PARAMETERS `α₀` AND `oα₀` ARE NOT USED BY ANY ROW.  They
-- are the module parameters of `L.SquareLawClosed`
-- (src/L/SquareLawClosed.lagda.md:19-20), and `κL` and its four
-- projections sit inside that module while their bodies never mention
-- them.  [LJ-1.638] measured the same trap on `inf-member` and
-- reported it as a PLACEMENT defect of src/
-- (agents/tasks/LJ-1-638/lj-1.638-report.md, "A second, smaller find").
-- This file pays the parameter rather than invent a value for it, so
-- the rows below stay generic in it (clause W2).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( IsOrd )

module LJ-1-640.Probe640
  {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; _↪_ )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; module Devlin55 )
open import L.CardinalAbove {ℓ} lem using ( ordL )
open import L.SquareLawClosed {ℓ} lem α₀ oα₀
  using ( κL; κoL; κ∈sucL; κ-injL; κ-min-atL )
import LJ-1-640.runs.W3
module W3 = LJ-1-640.runs.W3 lem

open Devlin55 using ( comp-inj )
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  WHAT A LEAST-CARDINAL SITE IS, AND THAT EVERY ONE OF
-- THEM IS AN AMBIENT CARDINAL.
-- =====================================================================

LeastSite : SL.S → Type (ℓ-suc ℓ)
LeastSite κ = Σ[ a ∈ SL.S ] Σ[ oa ∈ IsOrd (fst a) ] (κL a oa ≡ κ)

-- A member of `κL a oa` that `κL a oa` injected into would, composed
-- with `κ-injL`, give `fst a` an injection into that member, and
-- `κ-min-atL` refutes exactly that.  `κoL` is the site's ordinality,
-- which lifts the member to the L-carrier `κ-min-atL` quantifies over.
kappaL-is-ambient-cardinal :
    (a : SL.S) (oa : IsOrd (fst a)) → IsCardinal (fst (κL a oa))
kappaL-is-ambient-cardinal a oa δ δ∈κ f =
  κ-min-atL a oa δᴸ δ∈κ a↪δ
  where
  δᴸ : SL.S
  δᴸ = ordL δ (mem-ord {A = fst (κL a oa)} (κoL a oa) δ δ∈κ)

  a↪δ : ∥ ⟪ fst a ⟫ ↪ ⟪ δ ⟫ ∥₁
  a↪δ = PT.map (λ i → comp-inj i f) (κ-injL a oa)

least-site→amb : (κ : SL.S) → LeastSite κ → IsCardinal (fst κ)
least-site→amb κ (a , oa , e) =
  subst (λ z → IsCardinal (fst z)) e (kappaL-is-ambient-cardinal a oa)

-- =====================================================================
-- SECTION 2.  THE CONVERSE, AT `a := κ`.
-- =====================================================================

-- THE ONE PLACE THE MISSING INPUT IS SPENT, and it is spent at ONE
-- member and ONE injection: `κ∈sucL` puts `κL κ oκ` inside `sucV`, so
-- either it IS the site or it is a member of it, and the second
-- disjunct is refuted by the site's own ambient minimality applied to
-- `κ-injL`.  `↾-reflects` (src/FOL/ZFStructure.lagda.md:165-169)
-- carries the ambient equality back to the L-carrier.
least-at-self-pointwise :
    (κ : SL.S) (oκ : IsOrd (fst κ))
  → (⟨ fst (κL κ oκ) ∈ˢ fst κ ⟩
      → ∥ ⟪ fst κ ⟫ ↪ ⟪ fst (κL κ oκ) ⟫ ∥₁ → Empty.⊥)
  → κL κ oκ ≡ κ
least-at-self-pointwise κ oκ one = ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} fst≡
  where
  fst≡ : fst (κL κ oκ) ≡ fst κ
  fst≡ = ∈sucV-elim {A = fst κ} {x = fst (κL κ oκ)}
           (SV.isSetS (fst (κL κ oκ)) (fst κ))
           (κ∈sucL κ oκ)
           (λ h → Empty.rec (one h (κ-injL κ oκ)))
           (λ e → e)

amb→least-at-self :
    (κ : SL.S) (oκ : IsOrd (fst κ)) → IsCardinal (fst κ) → κL κ oκ ≡ κ
amb→least-at-self κ oκ amb =
  least-at-self-pointwise κ oκ
    (λ h → W3.amb-card→amb-minimal κ amb (κL κ oκ) h)

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
-- =====================================================================

bill-site-is-least :
    (κ : SL.S) (oκ : IsOrd (fst κ)) → IsCardinalL κ
  → IsCardinal (fst κ)
  → LeastSite κ
bill-site-is-least κ oκ cκ amb = κ , oκ , amb→least-at-self κ oκ amb

internal-is-redundant : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
internal-is-redundant = W3.delivered-direction

-- =====================================================================
-- SECTION 4.  THE NARROWING.
-- =====================================================================

bill-site-is-least-pointwise :
    (κ : SL.S) (oκ : IsOrd (fst κ))
  → (⟨ fst (κL κ oκ) ∈ˢ fst κ ⟩
      → ∥ ⟪ fst κ ⟫ ↪ ⟪ fst (κL κ oκ) ⟫ ∥₁ → Empty.⊥)
  → LeastSite κ
bill-site-is-least-pointwise κ oκ one =
  κ , oκ , least-at-self-pointwise κ oκ one

-- =====================================================================
-- SECTION 5.  WHAT THE MISSING INPUT BUYS DIRECTLY.
-- =====================================================================

amb→min-inputs :
    (κ : SL.S) → IsCardinal (fst κ)
  → (∥ ⟪ fst κ ⟫ ↪ ⟪ fst κ ⟫ ∥₁)
  × ((β : SV.S) → ⟨ β ∈ˢ fst κ ⟩ → ∥ ⟪ fst κ ⟫ ↪ ⟪ β ⟫ ∥₁ → Empty.⊥)
amb→min-inputs κ amb =
    ∣ (λ x → x) , (λ x y e → e) ∣₁
  , (λ β β∈κ → PT.rec Empty.isProp⊥ (amb β β∈κ))

-- =====================================================================
-- SECTION 6.  THE ANSWER TO THE BRIEF'S QUESTION, IN ONE TYPE.
--
--   Being a least-cardinal site and being an AMBIENT cardinal are the
--   SAME condition at an ordinal L-element.  Neither direction spends
--   `IsCardinalL`.  So the brief's question "is the bill's site a
--   least-cardinal site" has exactly one unpaid input, and that input
--   is `IsCardinal (fst κ)`.
--
--   THE C-42 SWEEP OVER src/ FOR THAT INPUT, COUNTED BEFORE ANY CURE
--   IS PRICED.
--
--   PRODUCERS of `IsCardinal` in src/: ONE.  `θ-card`
--   (src/L/CardinalAbove.lagda.md:160), and it produces one only at
--   the `θ` that `module Sep` (:118) BUILDS by separation, gated on
--   `⟨ θ ∈ˢ β ⟩`, which `θ∈β` (:174-178) pays from a member of β that
--   does NOT inject into `a`.  It says nothing about a site handed in
--   from outside.  `kappaL-is-ambient-cardinal` above is a SECOND
--   producer, at `κL a oa`, unconditional, and it costs four lines.
--
--   SITES where `IsCardinal` is DEMANDED at a campaign site and left
--   UNPAID as a module hypothesis: FOUR.
--     src/L/BoundedSubset.lagda.md:1386   `BoundedSubsetAt`, `cardκ`
--     src/L/BoundedSubset.lagda.md:1746   `BSA634`, `cardκ`
--     src/L/StageBound.lagda.md:65        `Instantiation`, `cardκ`
--     src/L/StageBound.lagda.md:94        the applying module, `cardκ`
--   Nothing in src/ applies any of the four with `cardκ` discharged:
--   `L.StageBound` is imported only by `src/Everything.lagda.md:396`.
--
--   SO THE MISSING INPUT IS NOT NEW TO CONJUNCT 4.  Devlin 5.5's whole
--   leg already carries it unpaid at the same kind of site.
-- =====================================================================

least-site⟺amb :
    (κ : SL.S) (oκ : IsOrd (fst κ))
  → (LeastSite κ → IsCardinal (fst κ))
  × (IsCardinal (fst κ) → LeastSite κ)
least-site⟺amb κ oκ =
    least-site→amb κ
  , (λ amb → κ , oκ , amb→least-at-self κ oκ amb)
