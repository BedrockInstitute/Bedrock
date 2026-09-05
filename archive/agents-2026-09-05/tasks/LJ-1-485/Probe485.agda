{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.485] W3 first: can ω∈γ be sourced at the [LJ-1.473] layout?
-- Layout from Probe473.agda:61-67, not imported. n = 9, carrier in
-- slot 0. Brief type ⟨ ω ∈ˢ fst gam ⟩ does not form. Predecessor
-- type ⟨ ω ∈ sucV gam ⟩ from EnvSupply.lagda.md:111 and
-- Probe467.agda:104. W3 is Countermodel.omega-source. The
-- obligation env-at-clause is not inhabited: ω∈γ has no source
-- at this telescope and the brief forbids gating it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-485.Probe485 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Condensation {ℓ} lem using ( module KValue )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open InfinitySet {ℓ} using ( sucV; ω; ω-next )
import Cubical.Data.Empty as Empty
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; ∅-ord )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- D-10.  someEnvDef vs the clause let-block, side by side.
--   someEnvDef (LowerAgree.lagda.md:52-58) takes three K-memberships
--   and no numeral fact.  PropAgree.back (Condensation.lagda.md:3505-3515)
--   binds arNum at :3509 from binary codesK and calls someEnv at :3515
--   without it.  SupplyEnv.someEnv (EnvSupply.lagda.md:417-424) also
--   takes ω∈γ at the module telescope (:111) and builds at B₀ = LsetS
--   gam.  This brief hypothesises the truncation.  Slot 0 is the
--   [LJ-1.473] filler.  ω∈γ has no source at this telescope.
-- =====================================================================

-- =====================================================================
-- W3.  ω∈γ at the [LJ-1.473] layout, obligation omitted.
--   Brief type ⟨ ω ∈ˢ fst gam ⟩ does not form: _∈ˢ_ is S → S → Ω
--   (ZFStructure.lagda.md:48-50) and gam is V ℓ
--   (Condensation.lagda.md:7384).  Predecessor type ⟨ ω ∈ sucV gam ⟩.
--   KValue accepts lam = ω and gam = ∅.  Carrier in slot 0 does not
--   exclude that instance.  omega-source: the type is empty there.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Carrier in slot 0, as [LJ-1.473] measured (Probe473.agda:61-64).
  -- Five remaining pad slots stay dummy.
  Kenv' : Vec S (11 + 9)
  Kenv' = LsetS gam ordγ ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  slot-zero : fst (lookup zero Kenv') ≡ fst (LsetS gam ordγ)
  slot-zero = refl

  -- The type the supplier takes, at this frame. Not inhabited here.
  -- The countermodel below shows it is empty at a legal instance.
  -- omega-source : ⟨ ω ∈ sucV gam ⟩

-- Legal instance of the KValue / [LJ-1.473] telescope.
-- lam = ω is successor-closed and contains ∅. gam = ∅ lies in ω.
-- Re-measured at this site, not transferred from [LJ-1.467].
module Countermodel where

  -- #∈ω 0 is ⟨ (# 0) ∈ ω ⟩ and # 0 is ∅ (V.Model.lagda.md:186,190).
  ∅∈ω : ⟨ ∅ ∈ ω ⟩
  ∅∈ω = #∈ω 0

  succω : (d : V ℓ) → ⟨ d ∈ ω ⟩ → ⟨ sucV d ∈ ω ⟩
  succω d d∈ω =
    ∈∈ₛ {a = sucV d} {b = ω} .snd
      (ω-next d (∈∈ₛ {a = d} {b = ω} .fst d∈ω))

  -- THIS layout at the legal instance. Carrier in slot 0.
  module Inst = W3 ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω

  carrier-at-instance :
      fst (lookup zero Inst.Kenv') ≡ fst (LsetS ∅ ∅-ord)
  carrier-at-instance = refl

  ω≢∅ : ω ≡ ∅ → Empty.⊥
  ω≢∅ e = ∈-irrefl ∅ (subst (λ w → ⟨ ∅ ∈ w ⟩) e ∅∈ω)

  ω∈∅-empty : ⟨ ω ∈ ∅ ⟩ → Empty.⊥
  ω∈∅-empty h = ∅-empty ω (∈∈ₛ {a = ω} {b = ∅} .fst h)

  -- W3. omega-source at the legal instance: the type is empty.
  -- Brief named ⟨ ω ∈ˢ fst gam ⟩. Predecessor type ⟨ ω ∈ sucV gam ⟩.
  -- At this instance the type is ⟨ ω ∈ sucV ∅ ⟩.
  omega-source : ⟨ ω ∈ sucV ∅ ⟩ → Empty.⊥
  omega-source h = ω∈∅-empty (∈sucV-elim (snd (ω ∈ ∅)) h
    (λ p → p)
    (λ e → Empty.rec (ω≢∅ e)))

-- =====================================================================
-- THE OBLIGATION.  env-at-clause is someEnvDef {9} with the
-- truncation added, carrier in slot 0, slot indices from
-- LowerAgree.lagda.md:52-58.  Countermodel.omega-source shows ω∈γ
-- has no source at this frame: the type is empty at a legal
-- instance.  The supplier cannot be applied.  No body.  No hole.
--
-- env-at-clause :
--     (ya yc b a ar c : S)
--   → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
--   → ⟨ fst ya ∈ fst (lookup (suc^6 iK') Kenv') ⟩
--   → ⟨ fst yc ∈ fst (lookup (suc^6 iK') Kenv') ⟩
--   → ⟨ fst ar ∈ fst (lookup (suc^6 iK') Kenv') ⟩
--   → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc^6 iK') Kenv') ⟩
--       × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv') ⊨
--             envHypB2 {11 + 9} zero (suc^6 iK') ⟩)
-- =====================================================================
