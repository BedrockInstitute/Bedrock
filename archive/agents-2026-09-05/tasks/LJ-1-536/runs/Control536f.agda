{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] CONTROL f.  THE SAME ROW WITH THE TOWER TAKEN OUT.
--
-- runs/Control536e.agda holds ONE obligation, `step-conv`, whose body
-- is the variable `p`, and it costs 425.73 s (runs/ctle-0.time).  That
-- row mentions four things: the `step` recursion, `sucV`, `Lset` and
-- `∈`.  `Lset` is `opaque` (src/L/Constructible.lagda.md:211, :221).
-- This file removes `Lset` and `∈` and keeps the rest, so a cheap run
-- says the cost is in the tower's reading and an expensive one says it
-- is in `sucV`.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth

module LJ-1-536.runs.Control536f {ℓ : Level} where

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

step-only : (α : V ℓ) → step 4 α ≡ step 3 (sucV α)
step-only α = refl
