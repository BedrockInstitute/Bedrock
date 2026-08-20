{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.420] PROBE.  Assemble the main chain into ONE term.
-- Lives in agents/tasks/LJ-1-420/ and lands nothing in src/.
--
--   W3 FIRST  `unfolding-cost`.  Join [LJ-1.406]'s sealed κL to
--             [LJ-1.413]'s sealed κL with one unfolding clause.
--             Typecheck this file ALONE before the rest of the chain.
--
--   TERM      `chain-upper`.  L.StageCardinal's own stage-card-upper,
--             after the pairing from [LJ-1.413] is plugged in.
--
-- ONE hypothesis: amb-to-coded at [LJ-1.414]'s delivered type
-- (Probe414.agda:134-139).  Not attempted.
--
-- ONE Agda process per run.  GHCRTS is the pane's caliber.  Untouched.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-420.Probe420 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode; IsCardinalL )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-401.Probe401 {ℓ} lem as P401
import LJ-1-406.Probe406 {ℓ} lem as P406
import LJ-1-411.Probe411 {ℓ} lem as P411
import LJ-1-412.Probe412 {ℓ} lem as P412
import LJ-1-413.Probe413 {ℓ} lem α₀ oα₀ as P413
import L.StageCardinal as StageCardinalMod

-- =====================================================================
-- W3.  The two κL seals are two atoms.  Direct application of
-- P406.init-at-kappa at P413's hypothesis type is UnequalTerms
-- (dev/pod/audit-2026-08-20.md, F10).  One unfolding clause joins
-- them.  The TYPE names 413's atom, so the consumer sees 413's seal.
-- The BODY unfolds both, so 406's term converts.
-- =====================================================================

opaque
  unfolding P406.κL P413.κL
  unfolding-cost :
      (a : S) (oa : IsOrd (fst a))
    → ⟨ ω ∈ˢ fst (P413.κL a oa) ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (P413.κL a oa) ⟩
         → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
    → Init (fst (P413.κL a oa))
  unfolding-cost = P406.init-at-kappa

-- =====================================================================
-- THE OBLIGATION.  One hypothesis: amb-to-coded at [LJ-1.414]'s
-- delivered type (Probe414.agda:134-139).  Every other piece is
-- imported.  The 414 conclusion becomes 413's ¬ IsCardinalL by the
-- definition of IsCardinalL (src/L/Cardinal.lagda.md:230-233).
-- =====================================================================

module _
  (amb-to-coded :
      (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
    → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
    → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
    → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁)
  where

  not-card-from-amb :
      (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
    → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
    → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
    → (IsCardinalL x → Empty.⊥)
  not-card-from-amb x ox ω∈x d d∈x infd arr card =
    card d d∈x (amb-to-coded x ox ω∈x d d∈x infd arr)

  pairing = P413.plugs-in unfolding-cost
              (P412.coded-descent (P411.code-as-data P401.isPropInjCode))
              not-card-from-amb

  module SC = StageCardinalMod lem α₀ oα₀ pairing

  chain-upper : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
              → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
  chain-upper = SC.Upper.stage-card-upper
