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

module LJ-1-534.runs.F {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

record F1 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    Ktr : isTransV (fst (Kslot K γ))

record F2 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    TK : ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩

record F3 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    numK0 : ⟨ # 0 ∈ fst (Kslot K γ) ⟩

record F4 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    sucK : (a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩
         → ⟨ sucV a ∈ fst (Kslot K γ) ⟩

record F5 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    pairK : (a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
          → ⟨ pr a b ∈ fst (Kslot K γ) ⟩

record F6 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    finSetK : (m : ℕ) (h : Fin m → V ℓ)
            → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
            → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩

record F7 {n : ℕ} (A : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    carrier≡ : lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ

record F8 {n : ℕ} (K : Fin (5 + n)) (γ : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    envSetK : (ar : S) (m : ℕ) → fst ar ≡ # m
            → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
            → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩
