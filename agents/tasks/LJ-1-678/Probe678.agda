{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.678] PROBE.  KValue, the adequate K both directions wait on.
-- It runs in agents/tasks/LJ-1-678/ and lands nothing in src/.
--
--   W3              suc-closure of a probe-local ω-block above a
--                   generic ordinal.  runs/W3.agda.
--   THE OBLIGATION  k-value.  KValue at that limit.  The HullStage
--                   telescope is not taken: succλ and ∅∈λ are terms.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-678.Probe678 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( IsOrd )
open import L.Condensation {ℓ} lem using ( module KValue )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
import LJ-1-678.runs.W3 {ℓ} lem as W3

-- W2: the ω-block is written once at a generic ordinal.  KValue
-- instantiates that carrier.  No fixed form.
module At (gam : V ℓ) (ordγ : IsOrd gam) where
  open W3.Block gam ordγ
  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  k-value = facts

k-value = At.k-value
