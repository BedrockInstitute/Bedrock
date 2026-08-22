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

module LJ-1-534.runs.G {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

-- [LJ-1.534] BISECTION 5.  The three conjuncts that carry NO transparent
-- V-constructor: Ktr, TK, numK0.  If this is green the wall of runs/F.agda
-- is not in them.
record F1 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    Ktr : isTransV (fst (Kslot K γ))

record F2 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    TK : ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩

record F3 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    numK0 : ⟨ # 0 ∈ fst (Kslot K γ) ⟩
