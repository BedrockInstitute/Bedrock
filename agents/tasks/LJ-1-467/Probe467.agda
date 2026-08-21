{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.467] W3 first, then the obligation someEnv-numeral.
-- Layout from [LJ-1.457] Probe457.agda:52-55 and :74-75, not from
-- that brief. n = 9: iK' : Fin 14, Kenv' : S ^ 20. W3 is W3.supplies,
-- the first of the three supplier hypotheses (ω∈γ) at this frame.
-- The obligation someEnv-numeral names the type; the body is from
-- SupplyEnv.someEnv only if W3 inhabits.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-467.Probe467 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open InfinitySet {ℓ} using ( sucV; ω; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.Data.Empty as Empty
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; ∅-ord )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- D-10.  someEnv vs someEnvDef, slots and hypotheses.
--   SupplyEnv.someEnv (EnvSupply.lagda.md:417-424) takes ω∈γ, the
--   numeral truncation, and B₀ = LsetS gam on a 4-slot frame.
--   someEnvDef (LowerAgree.lagda.md:52-58) takes none of those three
--   and reads B at slot 0 of γ.  KValue (Condensation.lagda.md:7380-7383)
--   does not carry ω∈γ.  [LJ-1.457] slot 0 is dummy numeralL 0.
-- =====================================================================

-- =====================================================================
-- W3.  First of the three: ω∈γ at [LJ-1.457]'s frame.
--   SupplyEnv takes ω∈γ : ⟨ ω ∈ sucV gam ⟩ (EnvSupply.lagda.md:111).
--   KValue's telescope is a limit bound and a stage below it
--   (Condensation.lagda.md:7380-7386).  The legal instance
--   lam = ω, gam = ∅ inhabits that telescope.  At that instance
--   the type is ⟨ ω ∈ sucV ∅ ⟩, which is empty.
--   Obligation omitted on the W3 runs.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Six dummy fillers, copied from Probe457.agda:52-55.
  Kenv' : Vec S (11 + 9)
  Kenv' = numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  -- The type the supplier takes, at this frame. Not inhabited here.
  -- The countermodel below shows it is empty at a legal instance.
  -- supplies : ⟨ ω ∈ sucV gam ⟩

-- Legal instance of the KValue / [LJ-1.457] telescope.
-- lam = ω is successor-closed and contains ∅ ([LJ-1.252] Countermodel).
-- gam = ∅ lies in ω.  Re-measured at this site, not transferred.
module Countermodel where

  -- #∈ω 0 is ⟨ (# 0) ∈ ω ⟩ and # 0 is ∅ (V.Model.lagda.md:186,190).
  ∅∈ω : ⟨ ∅ ∈ ω ⟩
  ∅∈ω = #∈ω 0

  succω : (d : V ℓ) → ⟨ d ∈ ω ⟩ → ⟨ sucV d ∈ ω ⟩
  succω d d∈ω =
    ∈∈ₛ {a = sucV d} {b = ω} .snd
      (ω-next d (∈∈ₛ {a = d} {b = ω} .fst d∈ω))

  -- The instance typechecks: KValue accepts these parameters.
  module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω

  ω≢∅ : ω ≡ ∅ → Empty.⊥
  ω≢∅ e = ∈-irrefl ∅ (subst (λ w → ⟨ ∅ ∈ w ⟩) e ∅∈ω)

  ω∈∅-empty : ⟨ ω ∈ ∅ ⟩ → Empty.⊥
  ω∈∅-empty h = ∅-empty ω (∈∈ₛ {a = ω} {b = ∅} .fst h)

  -- W3. supplies at the legal instance: the type is empty.
  supplies : ⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥
  supplies h = ω∈∅-empty (∈sucV-elim (snd (ω ∈ ∅)) h
    (λ p → p)
    (λ e → Empty.rec (ω≢∅ e)))

-- =====================================================================
-- THE OBLIGATION.  The type forms at n = 9: iK' : Fin (5 + 9) and
-- Kenv' : Vec S (11 + 9).  Countermodel.supplies shows ω∈γ has
-- no source at this frame: the type is empty at a legal instance.
-- The supplier cannot be applied.  No body.
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

someEnv-numeral :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → someEnvDef {9} iK' (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
someEnv-numeral = {!!}
