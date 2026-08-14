{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.261] closure probe: the three consK-* from [LJ-1.259] close with
-- finSetK SUPPLIED (ProbeLJ1261), together with numK0 and pairK from
-- L.Coding.Bound and sucK from [LJ-1.254] (already green there).  This is
-- the re-run the brief's abort criterion asks for: finSetK supplied rather
-- than assumed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-261.ProbeLJ1261Closure {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-layer; layer-trans )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

import LJ-1-261.ProbeLJ1261 {ℓ} lem as P1261
import LJ-1-259.ProbeLJ1259 {ℓ} as P1259
import LJ-1-254.ProbeLJ1254 {ℓ} lem as P1254

module Closure (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : S) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  open P1261.Supply lam ordλ succλ ∅∈λ

  module B = Bound lam ordλ succλ ∅∈λ

  module S1254 = P1254.Supply lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

  module F = P1259.Fact (P1259.levelK lam ordλ) (layer-trans (Lset-layer lam))

  module CC = F.ConsKClosed (B.#∈Tλ 0) S1254.sucK B.pr∈λ finSetK
