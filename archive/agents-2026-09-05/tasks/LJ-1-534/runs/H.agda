{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] BISECTION 3.  ONE record per field, in the collected
-- frame's own order.  Agda checks in order, so the first wall names the
-- field.  Green all through means no single field pays and the cost is
-- the combination.
--
-- Baseline: runs/I.agda, the same imports with no record, 1.04 s green.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.runs.H {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isTransV )
open import L.Axioms.Basic {ℓ} using ( finSet )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

Kslot : {n : ℕ} → Fin (5 + n) → Vec S (11 + n) → S
Kslot K γ = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

-- [LJ-1.534] BISECTION 6.  `sucK` ALONE, as a record field.  P-x
-- (dev/LESSONS.md:3630) and archive/dev/LJ-dispatch-index.md:234 both name
-- `sucK` as the waller at [LJ-1.158]'s site.  This re-measures it at THIS
-- site rather than transferring it (AGENTS.md:45).
record F4 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    sucK : (a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩
         → ⟨ sucV a ∈ fst (Kslot K γ) ⟩
