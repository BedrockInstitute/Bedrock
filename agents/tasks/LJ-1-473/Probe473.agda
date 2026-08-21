{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.473] W3 first: carrier in slot 0 of the [LJ-1.457] pad.
-- Layout from Probe457.agda:52-55 and :74-75, not from that brief.
-- n = 9: iK' : Fin 14, Kenv' : S ^ 20. Slot 0 is LsetS gam, not
-- dummy numeralL 0. W3 is W3.slot-zero. The obligation someEnv-gated
-- names the type; the body is a hole. Truncation has no source.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-473.Probe473 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Condensation {ℓ} lem using ( module KValue )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- D-10.  someEnv vs someEnvDef, slots and hypotheses.
--   SupplyEnv.someEnv (EnvSupply.lagda.md:417-424) takes ω∈γ, the
--   numeral truncation, and B₀ = LsetS gam on a 4-slot frame.
--   someEnvDef (LowerAgree.lagda.md:52-58) takes none of those three
--   and reads B at slot 0 of γ.  This frame states ω∈γ and puts the
--   carrier in slot 0.  The truncation has no source.
-- =====================================================================

-- =====================================================================
-- W3.  Carrier in slot 0, obligation omitted.
--   [LJ-1.457] put dummy numeralL 0 in all six pad slots
--   (Probe457.agda:52-55).  envHypB2 reads slot 0 as B.  The supplier
--   uses B₀ = LsetS gam (EnvSupply.lagda.md:124-125).  Put that
--   carrier in slot 0.  suc^6 still reads Kenv, so the 24-field
--   transfer of [LJ-1.457] does not see this slot.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Carrier in slot 0. Five remaining pad slots stay dummy.
  Kenv' : Vec S (11 + 9)
  Kenv' = LsetS gam ordγ ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  slot-zero : fst (lookup zero Kenv') ≡ fst (LsetS gam ordγ)
  slot-zero = refl

-- =====================================================================
-- THE OBLIGATION.  The type forms at n = 9: iK' : Fin (5 + 9) and
-- Kenv' : Vec S (11 + 9) with the carrier in slot 0.  ω∈γ is a stated
-- module hypothesis, type from EnvSupply.lagda.md:111, not the brief's
-- ill-typed ⟨ ω ∈ˢ fst gam ⟩.  The supplier still takes
-- ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁ (EnvSupply.lagda.md:418).  someEnvDef
-- does not.  No source.  The brief forbids gating it.  No body.
-- =====================================================================

iK' : Fin (5 + 9)
iK' = suc zero

Kenv' :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → Vec S (11 + 9)
Kenv' = W3.Kenv'

someEnv-gated :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
    (ω∈γ : ⟨ ω ∈ sucV gam ⟩)
  → someEnvDef {9} iK' (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
someEnv-gated = {!!}
