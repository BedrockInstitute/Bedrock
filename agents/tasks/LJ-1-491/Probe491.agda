{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.491] Rebuild KValue's telescope with ω∈γ. KFacts unchanged.
-- Census first: grep -rn "KValue" src/ is one hit, the definition
-- at Condensation.lagda.md:7380. The tree's own consumer is
-- consed via KFactsCons at :7429-7434, generic in gam. No src/
-- site applies KValue at a concrete stage.
--
-- Brief wrote ⟨ ω ∈ˢ gam ⟩. 𝒮ʟ's _∈ˢ_ is S → S → Ω
-- (ZFStructure.lagda.md:48). gam is V ℓ
-- (Condensation.lagda.md:7383). That type does not form under
-- 𝒮ʟ. 𝒮ᵥ's _∈ˢ_ is _∈_ (Hierarchy.lagda.md:83). This brief's
-- D-10 names ω ∈ gam. The type taken is ⟨ ω ∈ gam ⟩.
-- Predecessor 488's gate ⟨ ω ∈ sucV gam ⟩ is
-- EnvSupply.lagda.md:111, a weaker statement. This term does
-- not inhabit that weaker type.
--
-- Do not use ω∈γ in any field. Body is KValue.facts.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/. Do not import a probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-491.Probe491 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- D-10.  Adding ⟨ ω ∈ gam ⟩ excludes instances KValue accepts
--   today, including lam = ω, gam = ∅ ([LJ-1.467]
--   Probe467.agda:95, [LJ-1.476] Probe476.agda:63). The census
--   over src/ names no consumer that passes a finite gam. The
--   restriction is not refuted by a landed consumer.
-- =====================================================================

-- =====================================================================
-- THE OBLIGATION.  KValue's telescope plus ⟨ ω ∈ gam ⟩.
--   KFacts record unchanged. ω∈γ is not used in any field.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ gam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  kvalue-with-omega : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
  kvalue-with-omega = facts

kvalue-with-omega = W3.kvalue-with-omega
