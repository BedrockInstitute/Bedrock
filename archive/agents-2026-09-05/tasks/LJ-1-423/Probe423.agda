{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.423] PROBE.  The counting leg from ONE arrow.  It runs in
-- agents/tasks/LJ-1-423/ and lands nothing in src/.
--
--   W3 FIRST  `instantiation-cost`.  Instantiate L.StageCardinal with
--             a postulate-free stub pairing (a module parameter) and
--             read stage-card-upper.  Typechecked ALONE before the
--             real pairing is added.
--
--   TERM      `upper-from-arrow`.  The consumer's output at every band
--             ordinal, from descent-from-data (LJ-1.421) and
--             kappa-arrow-data (LJ-1.422) as module parameters.
--             No amb-to-coded, no coded-descent, no IsCardinalL.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty

module LJ-1-423.Probe423 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( isPropIsOrd; 𝒮ʟ )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
import L.StageCardinal
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Instantiation ALONE, postulate-free stub pairing.
-- The pairing is a module parameter.  Checking this module measures
-- instantiation-cost.  The real pairing is added after this is green.
-- =====================================================================

module Instantiation
  (pairing : (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
           → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
               ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
  where

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ pairing

  stub-upper : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
             → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
  stub-upper = SC.Upper.stage-card-upper

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- Plumbing for kappa-arrow-data's type.  Copied from [LJ-1.413]
-- Probe413.agda:136-137.  Not a hypothesis of upper-from-arrow.
-- =====================================================================
opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

-- The consumer's band membership produces the ordinal certificate the
-- chapter does not ask for.  Port of Probe413.agda:199-202.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

-- =====================================================================
-- THE OBLIGATION.  Two module hypotheses, at the types the 421 and 422
-- BRIEFS name, because neither report has delivered a verdict.  See the
-- report: the return is provisional.  No amb-to-coded, no coded-descent,
-- no IsCardinalL.
-- =====================================================================

module _
  (descent-from-data :
      (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x)
  (kappa-arrow-data :
      (a : S) (oa : IsOrd (fst a))
    → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
  where

  -- Named so the telescope carries the campaign's remaining arrow.
  -- descent-from-data's delivered type already internalized it; 423
  -- does not spend it in the pairing body.
  arrow-residue = kappa-arrow-data

  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

  step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = subst sq (sym x≡ω) squareω
    go (inr (inr ω∈x)) = descent-from-data x ox ω∈x ih'
      where
      ih' : (y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y
          → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y
      ih' y y∈x oy infy = ih y y∈x oy infy

  pairing :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)
  pairing δ δ∈ infδ = ∈-induction {P = Goal} step δ (band-ord δ δ∈) infδ

  module I = Instantiation pairing

  upper-from-arrow : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
                   → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
  upper-from-arrow = I.stub-upper
