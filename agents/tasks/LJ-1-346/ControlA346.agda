{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.346] THE LANDED SUPPLY, WIRED END TO END.
--
-- `[LJ-1.344]` supplied the two ties in its own file.  This file asks the
-- LANDED chapter for them: `L.Condensation.KTies` is now a module of the
-- delivered tree, and `L.Condensation.KValue` is the one `KFacts` value.
-- Both ties come out as CLOSED TERMS at the concrete 14-slot environment,
-- with every premise discharged except `KValue`'s own ordinal frame and
-- one named hypothesis that the carrier stage is at least 1.
--
-- IT ALSO MEASURES THE INTERFACE RULING.  Nothing here re-writes the
-- `private` block of `src/V/Coding.lagda.md`.  `sglS` reaches the pair
-- access through `L.Condensation.ChainZ.pair∈pr`, which the chapter has
-- carried in public since `[LJ-1.99]`, and `envOne-pair` is the new
-- public lemma the landing added.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-346.ControlA346 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt; envOne; envOneAt-in )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module KTies; module KValue; module ChainZ
        ; envOne-pair )
open KFactsNS

open hPropStructure 𝒮ʟ using ( S )

module KWire (lam : V ℓ) (ordλ : IsOrd lam)
             (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ lam ⟩)
             (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
             (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; pairK; carrierK; arityK )

  -- THE LANDED MODULE, AT THE DELIVERED RECORD.  Nothing is restated.
  open KTies KV.iA KV.iK KV.Kenv numK0 pairK carrierK arityK

  private
    module Z = ChainZ KV.iK KV.Kenv arityK

    tagged : S → S
    tagged z = prʟ (numeralL 0) z

    tagged-fst : (z : S) → fst (tagged z) ≡ pr (# 0) (fst z)
    tagged-fst z =
      prʟ-fst (numeralL 0) z ∙ cong (λ u → pr u (fst z)) (numeralL-fst 0)

    -- The singleton as a carrier element.  The pair access is the
    -- chapter's own public one, so this file carries NO copy of the
    -- `private` block of `src/V/Coding.lagda.md`.
    sglS : S → S
    sglS a = ⁅ fst a , fst a ⁆
           , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
               (subst (λ u → ⟨ ⁅ fst a , fst a ⁆ ∈ u ⟩) (sym (prʟ-fst a a))
                 (Z.pair∈pr (fst a) (fst a)))
               (snd (prʟ a a))

  liveE : S → S
  liveE z = sglS (tagged z)

  -- The one-entry environment, through the chapter's NEW public lemma.
  liveE-eq : (z : S) → fst (liveE z) ≡ envOne (fst z)
  liveE-eq z =
    sym (envOne-pair (fst z) ∙ cong (λ u → ⁅ u , u ⁆) (sym (tagged-fst z)))

  -- THE CARRIER IS INHABITED, so the ties fire on real arguments.
  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  -- CONTROL A, EXPECTED RED.  THE PRE-REPAIR TIE, which `[LJ-1.341]`
  -- proved FALSE and `[LJ-1.343]` repaired.  It drops the carrier
  -- hypothesis.  If the LANDED `KTies.envK` proved this too, the repair
  -- would be decoration in the type and not a constraint in the proof.
  -- The only term of any membership shape in scope is `h`, so offering
  -- `h` is the whole search.
  envK-unbounded : (E z : S)
                 → ⟨ (E ∷ z ∷ KV.Kenv) ⊨ envOneAt zero (suc zero) ⟩
                 → ⟨ fst E ∈ fst (lookup KV.iK KV.Kenv) ⟩
  envK-unbounded E z h = envK E z h h

  -- TIE 2 FIRES, AS A CLOSED TERM.
  defPairK-fires : ⟨ pr (# 0) (# 0) ∈ Lset lam ⟩
  defPairK-fires = subst (λ u → ⟨ u ∈ Lset lam ⟩)
    (prʟ-fst (numeralL 0) (numeralL 0)
      ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst 0))
    (defPairK (liveE (numeralL 0)) (numeralL 0) (tagged (numeralL 0))
      zero∈carrier premise)
    where
    premise : ⟨ (tagged (numeralL 0) ∷ liveE (numeralL 0) ∷ numeralL 0 ∷ KV.Kenv)
                ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
    premise = subst ⟨_⟩
      (sym (tagAtL-adequate zero 0 (suc (suc zero))
             (tagged (numeralL 0) ∷ liveE (numeralL 0) ∷ numeralL 0 ∷ KV.Kenv)))
      (tagged-fst (numeralL 0))
