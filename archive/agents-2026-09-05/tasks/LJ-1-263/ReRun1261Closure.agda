{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.263] re-run of ProbeLJ1261Closure against the MASTER.  The
-- local `finSetK` copy (P1261.Supply) is replaced by the master's
-- `FiniteSup`; `envConsK` comes via ReRun1259's `ConsKClosed`, and
-- `sucK` via ReRun1254 (which itself uses the master's
-- `union∈Lset-suc`).  C-45: everything lands from the master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-263.ReRun1261Closure {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-layer; layer-trans )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Coding.Key {ℓ} lem using ( module FiniteSup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

import LJ-1-263.ReRun1254 {ℓ} lem as R1254
import LJ-1-263.ReRun1259 {ℓ} lem as R1259

module Closure (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : S) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  open FiniteSup lam ordλ succλ ∅∈λ

  module B = Bound lam ordλ succλ ∅∈λ

  module S1254 = R1254.Supply lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

  module F = R1259.Fact (R1259.levelK lam ordλ) (layer-trans (Lset-layer lam))

  module CC = F.ConsKClosed (B.#∈Tλ 0) S1254.sucK B.pr∈λ finSetK
