{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.368 control B.  EXPECTED RED.  It lands nothing.  Repair it never.
--
-- THE REAL FIRST DATA GOAL.  `[LJ-1.365]` printed its first data goal at
-- `⟪ Lset α ⟫ ↪ ⟪ α ⟫` (SoloC2.agda:24-27).  That goal is reached only
-- by an assembly that wraps at the injection.  `Probe368.agda`'s
-- `one-rec-through-injection` is green and never wraps there.
--
-- The goal an assembly cannot avoid is BELOW: the band delivers
-- `∥ sq δ ∥₁` INSIDE its Pi (ProbeLJ1332A.agda:196-204), and
-- `L.StageCardinal` consumes `sq δ` (src/L/StageCardinal.lagda.md:
-- 17-19).  The naive proof of `BandChoice` runs the eliminator at the
-- motive `sq δ`.  Agda names that goal below.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-368.MustFail368B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem using ( LimitBandT )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- CONTROL B, SOLO.  The band's truncation, pushed out of the Pi.
band-choice : LimitBandT → ∥ LimitBand ∥₁
band-choice t =
  PT.∣ (λ δ oδ ω∈δ cl ni ih →
         PT.rec {P = sq δ} squash₁ (λ s → s) (t δ oδ ω∈δ cl ni ih)) ∣₁
