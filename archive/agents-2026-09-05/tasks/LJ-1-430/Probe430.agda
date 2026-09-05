{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.430] PROBE.  Select the least cardinal by the CODED predicate,
-- on the AMBIENT carrier.  Nothing lands in src/.
--
--   W3 FIRST  `coded-selects`.  CodedInjP' at hProp (ℓ-suc ℓ) on
--              ⟪ sucV (fst a) ⟫, then leastOf w lem.  Typechecked
--              ALONE, result discarded.  The level of lem at this
--              mixed pair is the whole risk.
--
--   TERM      `kappaC-ord`.  IsOrd (fst κC) by mem-ord along
--              member (sucV (fst a)) (fst selected).  Not written
--              until W3 is green.
--
--   MODULE HYPOTHESIS.  nonempty-coded is bare.  [LJ-1.429] owes it.
--              Not inhabited.  That task's probe is not imported.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-430.Probe430 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Cardinal {ℓ} lem using ( InjCode )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Ambient carrier, coded predicate, leastOf, result discarded.
-- Generic in a and in γ.  nonempty-coded is a bare module hypothesis.
-- Typechecked alone before kappaC-ord.
-- =====================================================================

module _ (a : S) (oa : IsOrd (fst a)) (γ : V ℓ) (oγ : IsOrd γ) where

  -- LeastCardInjL's crossing, rebuilt at the call site, not opened.
  -- src/L/Cardinal.lagda.md:72-80.
  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  -- The well-order is SEALED at the call site (P-i, R-36), as
  -- [LJ-1.421] seals κL at Probe421.agda:125-135 and as the chapter
  -- seals w at src/L/Cardinal.lagda.md:90-92.  An unsealed
  -- ⟪ sucV (fst a) ⟫ comparison unfolds the union representation
  -- (src/L/Cardinal.lagda.md:87-89).
  opaque
    w : SWO (⟪ sucV (fst a) ⟫)
    w = ordSWO (sucV (fst a)) (suc-ord oa)

  -- SiteBound.up's one line, restated at γ and oγ.
  -- src/L/Cardinal.lagda.md:171-172.
  upγ : Mem (Lset γ) → S
  upγ (x , m) = x , Lset→isL γ oγ x m

  CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' d = ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

  module _
    (nonempty-coded : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' d ⟩ ∥₁)
    where

    coded-selects : Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodedInjP' d
    coded-selects = leastOf w lem CodedInjP' nonempty-coded

    -- The ambient site's own two lines, src/L/Cardinal.lagda.md:125-127.
    selected = coded-selects
    κC       = upα (fst selected)

    kappaC-ord : IsOrd (fst κC)
    kappaC-ord = mem-ord {A = sucV (fst a)} (suc-ord oa) (fst κC)
                   (member (sucV (fst a)) (fst selected))
